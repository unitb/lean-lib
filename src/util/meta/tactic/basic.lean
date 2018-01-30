
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

meta def local_def_value (e : expr) : tactic expr := do
do (v,_) ← solve_aux `(true) (do
         (expr.elet n t v _) ← (revert e >> target)
           | fail format!"{e} is not a local definition",
         return v),
   return v

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

@[user_attribute]
meta def funext_attribte : user_attribute :=
{ name := `extensionality
, descr := "lemmas usable by `funext` tactic" }

attribute [extensionality] funext stream.ext array.ext

meta def ext1 (x : parse ident_ ?) : tactic unit :=
do ls ← attribute.get_instances `extensionality,
   ls.any_of (λ l, applyc l) <|> fail "no applicable extensionality rule found",
   interactive.intro x

meta def ext : parse ident_ * → tactic unit
 | [] := return ()
 | (x :: xs) := ext1 x >> ext xs

open list

meta def clear_except (xs : parse ident *) : tactic unit :=
do r  ← list.mmap get_local xs >>= revert_lst,
   local_context >>= mmap (try ∘ tactic.clear),
   intron r

meta def match_head (e : expr) : expr → tactic unit
| e' :=
    unify e e'
<|> do `(_ → %%e') ← whnf e',
       v ← mk_mvar,
       match_head (e'.instantiate_var v)

meta def find_matching_head : expr → list expr → tactic (list expr)
| e []         := return []
| e (H :: Hs) :=
  do t ← infer_type H,
     (cons H <$ match_head e t <|> pure id) <*> find_matching_head e Hs

meta def xassumption
  (asms : option (list expr) := none)
  (tac : tactic unit := return ()) : tactic unit :=
do { ctx ← asms.to_monad <|> local_context,
     t   ← target,
     hs   ← find_matching_head t ctx,
     hs.any_of (λ H, () <$ tactic.apply H ; tac) } <|>
do { exfalso,
     ctx ← asms.to_monad <|> local_context,
     t   ← target,
     hs   ← find_matching_head t ctx,
     hs.any_of (λ H, () <$ tactic.apply H ; tac) }
<|> fail "assumption tactic failed"
open nat
meta def auto_aux (asms : option (list expr) := none) : ℕ → tactic unit
| 0 := done
| (succ n) :=
xassumption asms $ auto_aux n

meta def auto (asms : option (list expr) := none) (depth := 3) : tactic unit :=
auto_aux asms depth

open tactic.interactive
open applicative (lift₂)

meta def tauto : tactic unit :=
repeat (do
  gs ← get_goals,
  () <$ intros ;
  casesm (some ()) [``(_ ∧ _),``(_ ∨ _),``(Exists _)] ;
  constructor_matching (some ()) [``(_ ∧ _),``(_ ↔ _)],
  gs' ← get_goals,
  guard (gs ≠ gs') ) ;
repeat
(refl <|> auto <|> constructor_matching none [``(_ ∧ _),``(_ ↔ _),``(Exists _)]) ;
done

meta def rw_aux (p : pos) (r : pexpr) (loc : loc) : tactic unit :=
do interactive.rw ⟨[rw_rule.mk p ff r ],none⟩ loc

meta def simp_coes
         (eta : parse (tk "!")?) (only_kw : parse only_flag)
         (rs : parse simp_arg_list) (atts : parse with_ident_list)
         (l : parse location)
: tactic unit := do
coes ← [``coe,``lift_t,``has_lift_t.lift,``coe_t,``has_coe_t.coe,``coe_b,``has_coe.coe,
        ``coe_fn, ``has_coe_to_fun.coe, ``coe_sort, ``has_coe_to_sort.coe].mmap
(λ n, simp_arg_type.expr <$> resolve_name n),
tactic.interactive.simp eta only_kw (rs ++ coes) atts l

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

meta def repeat1 (tac : tactic unit) : tactic unit :=
tac >> repeat tac

meta def simp_one_point
     (only_kw : parse only_flag)
     (rs : parse simp_arg_list)
     (atts : parse with_ident_list)
     (l : parse location) : tactic unit :=
soft_apply l
     (λ h, repeat1 $ one_point_at h.local_pp_name <|> simp none only_kw rs atts (loc.ns [h.local_pp_name]))
     (repeat1 $ one_point_at none <|> simp none only_kw rs atts (loc.ns [none]))

end tactic

open tactic
run_cmd add_interactive [`auto,`tauto,`xassumption,`unfold_local,`unfold_locals
                        ,`ext1,`ext,`clear_except
                        ,`distributivity,`print,`one_point,`simp_one_point]

meta def smt_tactic.interactive.break_asms : smt_tactic unit :=
tactic.split_all_or
meta def smt_tactic.interactive.auto : opt_param ℕ 3 → tactic unit
 | 0 := done
 | (nat.succ n) :=
do ls ← (local_context),
   ls.any_of (λ h, () <$ apply h ; smt_tactic.interactive.auto n)
     <|> exfalso ; smt_tactic.interactive.auto n
