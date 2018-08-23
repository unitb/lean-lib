
import data.stream
import util.control.applicative
import util.logic

namespace tactic

open tactic
open lean.parser
open interactive
open interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def get_local_value (e : expr) : tactic (option expr) :=
try_core $ local_def_value e

meta def print (e : parse texpr) : tactic unit :=
do e ← to_expr e,
   let e' := e.get_app_fn,
   if e'.is_local_constant
     then do p ← local_def_value e' >>= pp,
             trace format!"{e'.local_pp_name} := {p}"
   else if e'.is_constant
     then do e ← get_env, d ← e.get e'.const_name,
             p ← pp d.value,
             trace format!"{e'.const_name} := {p}"
     else do p ← pp e',
             trace format!"{p} := {e'.to_raw_fmt}"

meta def unfold_local (n : parse ident) : tactic unit := do
e ← resolve_name n >>= to_expr,
g ← target,
t ← infer_type e,
v ← mk_meta_var t,
h ← to_expr ``(%%e = (%%v : %%t)) >>= assert `h,
solve1 (do
  tactic.revert e,
  g ← target,
  match g with
   | (expr.elet n _ e b) := tactic.change (expr.instantiate_local n e b)
   | _ := fail $ to_string n ++ " is not a local definition"
  end,
  tactic.intros, reflexivity ),
rewrite_target h,
tactic.clear h

meta def unfold_locals : parse ident * → tactic unit
 | [] := return ()
 | (n::ns) := unfold_local n >> unfold_locals ns

open list

meta def clear_except (xs : parse ident *) : tactic unit :=
do let ns := name_set.of_list xs,
   local_context >>= mmap' (λ h : expr,
     when (¬ ns.contains h.local_pp_name) $
       try $ tactic.clear h) ∘ list.reverse

open tactic.interactive
open applicative (lift₂)

meta def rw_aux (p : pos) (r : pexpr) (loc : loc) : tactic unit :=
do interactive.rw ⟨[rw_rule.mk p ff r ],none⟩ loc

meta def simp_coes
         (eta : parse (tk "!")?) (only_kw : parse only_flag)
         (rs : parse simp_arg_list) (atts : parse with_ident_list)
         (l : parse location)
         (cfg : simp_config_ext := {})
: tactic unit := do
coes ← [``coe,``lift_t,``has_lift_t.lift,``coe_t,``has_coe_t.coe,``coe_b,``has_coe.coe,
        ``coe_fn, ``has_coe_to_fun.coe, ``coe_sort, ``has_coe_to_sort.coe].mmap
(λ n, simp_arg_type.expr <$> resolve_name n),
tactic.interactive.simp eta only_kw (rs ++ coes) atts l cfg

meta def distrib1
  (arg : rw_rule)
  (loc : loc) : tactic unit :=
do let op := arg.rule,
   let p := arg.1,
   if arg.symm then
   ( rw_aux p ``(is_left_distrib.left_distrib _ %%op) loc <|>
     rw_aux p ``(is_right_distrib.right_distrib _ %%op) loc)
   else
   ( rw_aux p ``(is_left_distrib.left_distrib %%op) loc <|>
     rw_aux p ``(is_right_distrib.right_distrib %%op) loc),
   return ()

meta def distributivity
  (args : parse $ rw_rules)
  (l : parse location) : tactic unit :=
mmap' (λ e, distrib1 e l) args.rules

meta def split_or (xs : list expr) : smt_tactic (list expr) :=
do cs ← local_context,
   h ← mmap (λ h, try_core $ do
     t ← infer_type h,
     h <$ (match_or t <|> match_and t))
   $ cs.diff xs,
  let h' := h.filter_map id,
  h' <$ mmap' smt_tactic.destruct h'

meta def split_all_or' : list expr → smt_tactic unit
 | xs := do ys ← split_or xs, (guard (¬ ys.empty) >> smt_tactic.all_goals (split_all_or' (ys ++ xs))) <|> return ()

meta def split_all_or : smt_tactic unit :=
split_all_or' []

/--  (w,p) ← find_eq e returns a witness for bound variable #0 and a proof that
 -   the witness is valid
 -/
meta def find_eq (v : expr) : expr → tactic (expr × expr)
 | `(%%p ∧ %%q) :=
(do (w,pr) ← whnf p >>= find_eq,
    pr' ← to_expr ``(λ p : %%p ∧ %%q, %%pr ∘ and.elim_left $ p),
    return (w,pr')) <|>
(do (w,pr) ← whnf q >>= find_eq,
    pr' ← to_expr ``(λ p : %%p ∧ %%q, %%pr ∘ and.elim_right $ p),
    return (w,pr'))
 | e@`(@Exists %%t %%p') :=
do  (expr.lam n bi _ p) ← pure p',
    v ← mk_local' n bi t,
    let p'' := p.instantiate_var v,
    (w,pr) ← whnf p'' >>= find_eq,
    pr' ← to_expr ``( (exists_imp_iff_forall_imp _ _).mpr %%(pr.lambdas [v])),
    return (w,pr')
 | `(%%e₀ = %%e₁) := do
   if e₀ = v then do
      guard (¬ e₁.occurs v),
      p ← to_expr ``(@id (%%e₀ = %%e₁)), return (e₁,p)
   else if e₁ = v then do
      guard (¬ e₀.occurs v),
      p ← to_expr ``(@eq.symm _ %%e₀ %%e₁), return (e₀,p)
   else failed
 | _ := failed

meta def one_point_aux : expr → tactic (expr × expr)
 | e@`(@Exists %%t %%p') :=
(do (expr.lam n bi _ p) ← pure p',
    v ← mk_local' n bi t,
    let p'' := p.instantiate_var v,
    (w,pr) ← whnf p'' >>= find_eq v,
    let pr' := pr.lambdas [v],
    pr'' ← to_expr ``(iff.to_eq (exists_one_point %%w %%pr')),
    let p' := p.instantiate_var w,
    return (p',pr'')) <|>
(do (expr.lam n bi _ p) ← pure p',
    v ← mk_local' n bi t,
    let p'' := p.instantiate_var v,
    (e',pr) ← one_point_aux p'',
    e'' ← to_expr ``(Exists %%(e'.lambdas[v])),
    pr' ← to_expr ``(eq.to_iff %%pr),
    pr'' ← to_expr ``(iff.to_eq (exists_congr %%(pr'.lambdas [v]))),
    return (e'',pr''))
 | e₀@(expr.lam n bi t e₁) :=
do  v ← mk_local' n bi t,
    (e',pr) ← one_point_aux (e₁.instantiate_var v),
    let pr' := pr.lambdas [v],
    pr'' ← to_expr ``(@_root_.funext %%t _ %%e₀ %%(e'.lambdas [v]) %%pr'),
    return (e'.lambdas [v],pr'')
 | (expr.app e₀ e₁) :=
(do (e',pr) ← one_point_aux e₀,
    pr' ← to_expr ``(congr_fun %%pr %%e₁),
    return (expr.app e' e₁,pr')) <|>
(do (e',pr) ← one_point_aux e₁,
    pr' ← to_expr ``(congr_arg %%e₀ %%pr),
    return (expr.app e₀ e',pr'))
--  | `(%%e₀ → %%e₁) :=
-- do guard (e₁.has_var_idx 0),
--    (do (e',pr) ← one_point_aux e₀, _) <|>
--    (do (e',pr) ← one_point_aux e₁, _)
 | _ := failed

meta def soft_apply : loc → (expr → tactic unit) → tactic unit → tactic unit
 | l@loc.wildcard asm tgt := l.try_apply asm tgt
 | l asm tgt := l.apply asm tgt

meta def one_point_at : option name → tactic unit
| (some h) :=
  do h ← get_local h,
     t ← infer_type h,
     (t',pr) ← one_point_aux t,
     () <$ replace_hyp h t' pr
| none :=
  do t ← target,
     (t',pr) ← one_point_aux t,
     replace_target t' pr

meta def one_point (l : parse location) : tactic unit :=
soft_apply l
(λ h, one_point_at h.local_pp_name)
(one_point_at none)

/-- simplify `∃ x, ... x = y ...` and delete `x` -/
meta def simp_one_point
     (only_kw : parse only_flag)
     (rs : parse simp_arg_list)
     (atts : parse with_ident_list)
     (l : parse location) : tactic unit :=
soft_apply l
     (λ h, repeat1 $ one_point_at h.local_pp_name <|> simp none only_kw rs atts (loc.ns [h.local_pp_name]))
     (repeat1 $ one_point_at none <|> simp none only_kw rs atts (loc.ns [none]))

meta def set_binder' : expr → binder_info → expr
 | (expr.pi v _ d b) bi := expr.pi v bi d (set_binder' b bi)
 | e _ := e

open expr
meta def pis' : list expr → expr → tactic expr
| (e@(local_const uniq pp info _) :: es) f := do
  t ← infer_type e,
  f' ← pis' es f,
  pure $ pi pp info t (abstract_local f' uniq)
| _ f := pure f

meta def update_name (f : string → string) : name → name
 | (name.mk_string s p) := name.mk_string (f s) p
 | x := x <.> f ""

meta def strip_prefix : name → name
 | (name.mk_string s p) := name.mk_string s name.anonymous
 | (name.mk_numeral s p) := name.mk_numeral s name.anonymous
 | name.anonymous := name.anonymous

protected meta def mk_unique_name' (n : name) : ℕ → tactic name | i :=
do let n' := update_name (λ x, x ++ "_" ++ to_string i) n,
   (resolve_name n' >> mk_unique_name' (i+1)) <|> pure n'

meta def mk_unique_name (n : name) : tactic name :=
(resolve_name n >> tactic.mk_unique_name' n 1) <|> pure n

meta def my_generalize
     (n : parse $ ident <* tk ":")
     (p : parse texpr)
     (h : parse (tk "with" *> ident)?): tactic unit :=
do u ← mk_meta_univ,
   t ← mk_meta_var (expr.sort u),
   tgt ← target,
   v ← mk_meta_var t,
   -- (fail "thus far" : tactic unit),
   t ← to_expr ``(%%t → %%tgt),
   (p,_) ← solve_aux t (do
     n ← intro n,
     p ← to_expr p,
     return $ expr.instantiate_var (expr.abstract p n) v),
   unify p tgt,
   interactive.generalize h () (to_pexpr v,n),
   instantiate_mvars v >>= trace

meta def explicit_binders : tactic unit :=
do t ← target,
   h ← assert `h $ set_binder' t binder_info.default,
   tactic.swap,
   exact h

meta def revert' (ids : parse ident*) : tactic unit :=
propagate_tags (do hs ← mmap tactic.get_local ids, revert_lst hs, explicit_binders, skip)

end tactic

open tactic
run_cmd add_interactive [`unfold_local,`unfold_locals
                        ,`clear_except,`simp_coes,`explicit_binders
                        ,`distributivity,`print,`one_point,`simp_one_point,`revert'
                        ,`my_generalize]

meta def smt_tactic.interactive.break_asms : smt_tactic unit :=
tactic.split_all_or
meta def smt_tactic.interactive.auto : opt_param ℕ 3 → tactic unit
 | 0 := done
 | (nat.succ n) :=
do ls ← (local_context),
   ls.any_of (λ h, () <$ apply h ; smt_tactic.interactive.auto n)
     <|> exfalso ; smt_tactic.interactive.auto n
