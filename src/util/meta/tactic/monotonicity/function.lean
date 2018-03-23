
import util.algebra.group -- do not delete: imports instances

import util.data.list
import util.data.ulift_t
import util.meta.expr
import util.meta.tactic.basic

variables {a b c p : Prop}

namespace tactic.interactive

open lean lean.parser  interactive
open interactive.types
open tactic

local postfix `?`:9001 := optional
local postfix *:9001 := many

structure monotonicity_cfg :=
  (unify := ff)

meta inductive mono_function (elab : bool := tt)
 | non_assoc : expr elab → list (expr elab) → list (expr elab) → mono_function
 | assoc : expr elab → option (expr elab) → option (expr elab) → mono_function
 | assoc_comm : expr elab → expr elab → mono_function

meta instance : decidable_eq mono_function :=
by mk_dec_eq_instance

meta def mono_function.to_tactic_format : mono_function → tactic format
 | (mono_function.non_assoc fn xs ys) := do
  fn' ← pp fn,
  xs' ← mmap pp xs,
  ys' ← mmap pp ys,
  return format!"{fn'} {xs'} _ {ys'}"
 | (mono_function.assoc fn xs ys) := do
  fn' ← pp fn,
  xs' ← pp xs,
  ys' ← pp ys,
  return format!"{fn'} {xs'} _ {ys'}"
 | (mono_function.assoc_comm fn xs) := do
  fn' ← pp fn,
  xs' ← pp xs,
  return format!"{fn'} _ {xs'}"

meta instance has_to_tactic_format_mono_function : has_to_tactic_format mono_function :=
{ to_tactic_format := mono_function.to_tactic_format }

meta structure mono_ctx' (rel : Type) :=
  (to_rel : rel)
  (function : mono_function)
  (left right rel_def : expr)

@[reducible]
meta def mono_ctx := mono_ctx' (option (expr → expr → expr))
@[reducible]
meta def mono_ctx_ne := mono_ctx' (expr → expr → expr)

meta instance : has_traverse mono_ctx' :=
by derive_traverse

meta def mono_ctx.to_tactic_format (ctx : mono_ctx) : tactic format :=
do fn  ← pp ctx.function,
   l   ← pp ctx.left,
   r   ← pp ctx.right,
   rel ← pp ctx.rel_def,
   return format!"{{ function := {fn}\n, left  := {l}\n, right := {r}\n, rel_def := {rel} }"

meta instance has_to_tactic_format_mono_ctx : has_to_tactic_format mono_ctx :=
{ to_tactic_format := mono_ctx.to_tactic_format }

meta def as_goal (e : expr) (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   set_goals [e],
   tac,
   set_goals gs

open list (hiding map) functor dlist monad (mmap₂')

section config

parameter opt : monotonicity_cfg
parameter asms : list expr

meta def unify_with_instance (e : expr) : tactic unit :=
as_goal e $
apply_instance
<|>
apply_opt_param
<|>
apply_auto_param
<|>
solve_by_elim (some asms)
<|>
return ()

private meta def match_rule_head (p : expr)
: list expr → expr → expr → tactic expr
 | vs e t :=
(unify t p >> mmap' unify_with_instance vs.tail >> instantiate_mvars e)
<|>
do (expr.pi _ _ d b) ← return t | failed,
   v ← mk_meta_var d,
   match_rule_head (v::vs) (expr.app e v) (b.instantiate_var v)

meta def pi_head : expr → tactic expr
| (expr.pi n _ t b) :=
do v ← mk_meta_var t,
   pi_head (b.instantiate_var v)
| e := return e

def last_two {α : Type*} : list α → option (α × α)
| [] := none
| [x] := none
| (x₀ :: x₁ :: xs) := last_two (x₁ :: xs) <|> some (x₀, x₁)

meta def compare (e₀ e₁ : expr) : tactic unit := do
if opt.unify then do
guard (¬ e₀.is_mvar ∧ ¬ e₁.is_mvar),
unify e₀ e₁
else is_def_eq e₀ e₁

meta def find_one_difference
: list expr → list expr → tactic (list expr × expr × expr × list expr)
 | (x :: xs) (y :: ys) :=
   do c ← try_core (compare x y),
      if c.is_some
      then prod.map (cons x) id <$> find_one_difference xs ys
      else do
        guard (xs.length = ys.length),
        mmap₂' compare xs ys,
        return ([],x,y,xs)
 | xs ys := fail format!"find_one_difference: {xs}, {ys}"

meta def delete_expr (e : expr)
: list expr → tactic (option (list expr))
 | [] := return none
 | (x :: xs) :=
(compare e x >> return (some xs))
<|>
(map (cons x) <$> delete_expr xs)

meta def match_ac'
: list expr → list expr → tactic (list expr × list expr × list expr)
 | es (x :: xs) := do
    es' ← delete_expr x es,
    match es' with
     | (some es') := do
       (c,l,r) ← match_ac' es' xs, return (x::c,l,r)
     | none := do
       (c,l,r) ← match_ac' es xs, return (c,l,x::r)
    end
 | es [] := do
return ([],es,[])

meta def match_ac (unif : bool) (l : list expr) (r : list expr)
: tactic (list expr × list expr × list expr) :=
do (s',l',r') ← match_ac' l r,
   s' ← mmap instantiate_mvars s',
   l' ← mmap instantiate_mvars l',
   r' ← mmap instantiate_mvars r',
   return (s',l',r')

meta def match_prefix
: list expr → list expr → tactic (list expr × list expr × list expr)
| (x :: xs) (y :: ys) :=
  (do compare x y,
      prod.map ((::) x) id <$> match_prefix xs ys)
<|> return ([],x :: xs,y :: ys)
| xs ys := return ([],xs,ys)

/--
`(prefix,left,right,suffix) ← match_assoc unif l r` finds the
longest prefix and suffix common to `l` and `r` and
returns them along with the differences  -/
meta def match_assoc (l : list expr) (r : list expr)
: tactic (list expr × list expr × list expr × list expr) :=
do (pre,l₁,r₁) ← match_prefix l r,
   (suf,l₂,r₂) ← match_prefix (reverse l₁) (reverse r₁),
   return (pre,reverse l₂,reverse r₂,reverse suf)

meta def check_ac : expr → tactic (bool × bool × option (expr × expr × expr) × expr)
 | (expr.app (expr.app f x) y) :=
   do t ← infer_type x,
      a ← try_core $ to_expr ``(is_associative %%t %%f) >>= mk_instance,
      c ← try_core $ to_expr ``(is_commutative %%t %%f) >>= mk_instance,
      i ← try_core (do
          v ← mk_meta_var t,
          l_inst_p ← to_expr ``(is_left_id %%t %%f %%v),
          r_inst_p ← to_expr ``(is_right_id %%t %%f %%v),
          l_v ← mk_meta_var l_inst_p,
          r_v ← mk_meta_var r_inst_p ,
          l_id ← mk_mapp `is_left_id.left_id [some t,f,v,some l_v],
          mk_instance l_inst_p >>= unify l_v,
          r_id ← mk_mapp `is_right_id.right_id [none,f,v,some r_v],
          mk_instance r_inst_p >>= unify r_v,
          v' ← instantiate_mvars v,
          return (l_id,r_id,v')),
      return (a.is_some,c.is_some,i,f)
 | _ := return (ff,ff,none,expr.var 1)

meta def parse_assoc_chain' (f : expr) : expr → tactic (dlist expr)
 | e :=
 (do (expr.app (expr.app f' x) y) ← return e,
     is_def_eq f f',
     (++) <$> parse_assoc_chain' x <*> parse_assoc_chain' y)
<|> return (singleton e)

meta def parse_assoc_chain (f : expr) : expr → tactic (list expr) :=
map dlist.to_list ∘ parse_assoc_chain' f

meta def fold_assoc (op : expr) : option (expr × expr × expr) → list expr → option (expr × list expr)
| _ (x::xs) := some (foldl (expr.app ∘ expr.app op) x xs, [])
| none []   := none
| (some (l_id,r_id,x₀)) [] := some (x₀,[l_id,r_id])

meta def fold_assoc1 (op : expr) : list expr → option expr
| (x::xs) := some $ foldl (expr.app ∘ expr.app op) x xs
| []   := none

meta def same_function_aux
: list expr → list expr → expr → expr → tactic (expr × list expr × list expr)
 | xs₀ xs₁ (expr.app f₀ a₀) (expr.app f₁ a₁) :=
   same_function_aux (a₀ :: xs₀) (a₁ :: xs₁) f₀ f₁
 | xs₀ xs₁ e₀ e₁ := is_def_eq e₀ e₁ >> return (e₀,xs₀,xs₁)

meta def same_function : expr → expr → tactic (expr × list expr × list expr) :=
same_function_aux [] []

meta def parse_mono_function (l r : expr)
: tactic (expr × expr × list expr × mono_function) :=
do (full_f,ls,rs) ← same_function l r,
   (a,c,i,f) ← check_ac l,
   if a
   then if c
   then do
     (s,ls,rs) ← monad.join (match_ac tt
                   <$> parse_assoc_chain f l
                   <*> parse_assoc_chain f r),
     (l',l_id) ← fold_assoc f i ls,
     (r',r_id) ← fold_assoc f i rs,
     s' ← fold_assoc1 f s,
     return (l',r',l_id ++ r_id,mono_function.assoc_comm f s')
   else do -- a ∧ ¬ c
     (pre,ls,rs,suff) ← monad.join (match_assoc
                   <$> parse_assoc_chain f l
                   <*> parse_assoc_chain f r),
     (l',l_id) ← fold_assoc f i ls,
     (r',r_id) ← fold_assoc f i rs,
     let pre'  := fold_assoc1 f pre,
     let suff' := fold_assoc1 f suff,
     return (l',r',l_id ++ r_id,mono_function.assoc f pre' suff')
   else do -- ¬ a
     (xs₀,x₀,x₁,xs₁) ← find_one_difference ls rs,
     return (x₀,x₁,[],mono_function.non_assoc full_f xs₀ xs₁)

meta def parse_mono_function' (l r : pexpr) :=
do l' ← to_expr l,
   r' ← to_expr r,
   parse_mono_function l' r'

meta def monotonicity_goal : expr → tactic (expr × expr × list expr × mono_ctx)
 | `(%%e₀ → %%e₁) :=
  do (l,r,id_rs,f) ← parse_mono_function e₀ e₁,
     t₀ ← infer_type e₀,
     t₁ ← infer_type e₁,
     rel_def ← to_expr ``(λ x₀ x₁, (x₀ : %%t₀) → (x₁ : %%t₁)),
     return (e₀, e₁, id_rs,
            { function := f
            , left := l, right := r
            , to_rel := some $ expr.pi `x binder_info.default
            , rel_def := rel_def })
 | `(%%e₀ = %%e₁) :=
  do (l,r,id_rs,f) ← parse_mono_function e₀ e₁,
     t₀ ← infer_type e₀,
     t₁ ← infer_type e₁,
     rel_def ← to_expr ``(λ x₀ x₁, (x₀ : %%t₀) = (x₁ : %%t₁)),
     return (e₀, e₁, id_rs,
            { function := f
            , left := l, right := r
            , to_rel := none
            , rel_def := rel_def })
 | (expr.app (expr.app rel e₀) e₁) :=
  do (l,r,id_rs,f) ← parse_mono_function e₀ e₁,
     return (e₀, e₁, id_rs,
            { function := f
            , left := l, right := r
            , to_rel := expr.app ∘ expr.app rel
            , rel_def := rel })
 | _ := fail "invalid monotonicity goal"

meta def bin_op_left (f : expr)  : option expr → expr → expr
| none e := e
| (some e₀) e₁ := f.mk_app [e₀,e₁]

meta def bin_op (f a b : expr) : expr :=
f.mk_app [a,b]

meta def bin_op_right (f : expr) : expr → option expr → expr
| e none := e
| e₀ (some e₁) := f.mk_app [e₀,e₁]

meta def mk_fun_app : mono_function → expr → expr
 | (mono_function.non_assoc f x y) z := f.mk_app (x ++ z :: y)
 | (mono_function.assoc f x y) z := bin_op_left f x (bin_op_right f z y)
 | (mono_function.assoc_comm f x) z := f.mk_app [z,x]

meta inductive mono_law
   /- `assoc (l₀,r₀) (r₁,l₁)` gives first how to find rules to prove
      x+(y₀+z) R x+(y₁+z);
      if that fails, helps prove (x+y₀)+z R (x+y₁)+z -/
 | assoc : expr × expr → expr × expr → mono_law
   /- `congr r` gives the rule to prove `x = y → f x = f y` -/
 | congr : expr → mono_law
 | other : expr → mono_law

meta def mono_law.to_tactic_format : mono_law → tactic format
 | (mono_law.other e) := do e ← pp e, return format!"other {e}"
 | (mono_law.congr r) := do e ← pp r, return format!"congr {e}"
 | (mono_law.assoc (x₀,x₁) (y₀,y₁)) :=
do x₀ ← pp x₀,
   x₁ ← pp x₁,
   y₀ ← pp y₀,
   y₁ ← pp y₁,
   return format!"assoc {x₀}; {x₁} | {y₀}; {y₁}"

meta instance has_to_tactic_format_mono_law : has_to_tactic_format mono_law :=
{ to_tactic_format := mono_law.to_tactic_format }

meta def mk_rel (ctx : mono_ctx_ne) (f : expr → expr) : expr :=
ctx.to_rel (f ctx.left) (f ctx.right)

meta def mk_congr_args (fn : expr) (xs₀ xs₁ : list expr) (l r : expr) : tactic expr :=
do p ← mk_app `eq [fn.mk_app $ xs₀ ++ l :: xs₁,fn.mk_app $ xs₀ ++ r :: xs₁],
   prod.snd <$> solve_aux p
     (do iterate_exactly (xs₁.length) (applyc `congr_fun),
         applyc `congr_arg)

meta def mk_congr_law (ctx : mono_ctx) : tactic expr :=
match ctx.function with
 | (mono_function.assoc f x₀ x₁) :=
    if (x₀ <|> x₁).is_some
       then mk_congr_args f x₀.to_monad x₁.to_monad ctx.left ctx.right
       else failed
 | (mono_function.assoc_comm f x₀) := mk_congr_args f [x₀] [] ctx.left ctx.right
 | (mono_function.non_assoc f x₀ x₁) := mk_congr_args f x₀ x₁ ctx.left ctx.right
end

meta def mk_pattern (ctx : mono_ctx) : tactic mono_law :=
match (sequence ctx : option (mono_ctx' _)) with
 | (some ctx) :=
   match ctx.function with
    | (mono_function.assoc f (some x) (some y)) :=
      return $ mono_law.assoc
       ( mk_rel ctx (λ i, bin_op f x (bin_op f i y))
       , mk_rel ctx (λ i, bin_op f i y))
       ( mk_rel ctx (λ i, bin_op f (bin_op f x i) y)
       , mk_rel ctx (λ i, bin_op f x i))
    | (mono_function.assoc f (some x) none) :=
      return $ mono_law.other $
        mk_rel ctx (λ e, mk_fun_app ctx.function e)
    | (mono_function.assoc f none (some y)) :=
      return $ mono_law.other $
        mk_rel ctx (λ e, mk_fun_app ctx.function e)
    | (mono_function.assoc f none none) :=
      none
    | _ :=
      return $ mono_law.other $
         mk_rel ctx (λ e, mk_fun_app ctx.function e)
   end
 | none := mono_law.congr <$> mk_congr_law ctx
end

meta def match_rule (pat : expr) (r : name) : tactic expr :=
do  r' ← mk_const r,
    t  ← infer_type r',
    match_rule_head pat [] r' t

meta def find_lemma (pat : expr) : list name → tactic (list expr)
 | [] := return []
 | (r :: rs) :=
 do (cons <$> match_rule pat r <|> pure id) <*> find_lemma rs

meta def match_chaining_rules (ls : list name) (x₀ x₁ : expr) : tactic (list expr) :=
do x' ← to_expr ``(%%x₁ → %%x₀),
   r₀ ← find_lemma x' ls,
   r₁ ← find_lemma x₁ ls,
   return (expr.app <$> r₀ <*> r₁)

meta def find_rule (ls : list name) : mono_law → tactic (list expr)
 | (mono_law.assoc (x₀,x₁) (y₀,y₁)) :=
(match_chaining_rules ls x₀ x₁)
<|> (match_chaining_rules ls y₀ y₁)
 | (mono_law.congr r) := return [r]
 | (mono_law.other p) := find_lemma p ls

universes u v

lemma apply_rel {α : Sort u} (R : α → α → Sort v) {x y : α}
  (x' y' : α)
  (h : R x y)
  (hx : x = x')
  (hy : y = y')
: R x' y' :=
by { rw [← hx,← hy], apply h }

meta def one_line (e : expr) : tactic format :=
do lbl ← pp e,
   asm ← infer_type e >>= pp,
   return format!"\t{asm}\n"

meta def side_conditions (e : expr) : tactic format :=
do let vs := e.list_meta_vars,
   ts ← mmap one_line vs.tail,
   let r := e.get_app_fn.const_name,
   return format!"{r}:\n{format.join ts}"

meta def my_ac_refl : tactic unit :=
do g ← target >>= instantiate_mvars,
   let vs := g.list_meta_vars,
   vs' ← mmap (λ v, try_core $ tactic.generalize v) vs,
   intron (filter_map id vs').length,
   ac_refl

meta def my_ac_refl' : tactic unit :=
do (l,r) ← target >>= match_eq,
   let fn := l.app_fn.app_fn,
   a ← to_expr ``(is_associative %%fn) >>= mk_instance,
   c ← to_expr ``(is_commutative %%fn) >>= mk_instance,
   e ← perm_ac fn a c l r, tactic.exact e

meta def generalize_meta_vars : tactic (expr × list expr × expr) :=
do tgt ← target >>= instantiate_mvars,
   tactic.change tgt,
   let vs := tgt.list_meta_vars,
   ⟨(v,tgt'), _⟩ ← solve_aux tgt
     (do vs' ← mmap (λ v, tactic.generalize v `x >> intro1) vs.reverse,
         v ← mk_mvar,
         h ← note `h none v,
         tactic.revert h,
         n ← revert_lst vs',
         prod.mk v <$> target),
   return (v,vs,tgt')

open monad

private meta def hide_meta_vars (tac : list expr → itactic) : tactic unit :=
do (v,args,t) ← generalize_meta_vars,
   h ← assert `h t,
   solve1 (do
     ctx ← local_context,
     tactic.intron args.length,
     x ← intro1,
     tac ctx,
     tactic.exact x),
   tactic.apply (h.mk_app args),
   tactic.clear h

meta def hide_meta_vars' (tac : itactic) : itactic :=
hide_meta_vars $ λ _, tac

end config

meta def solve_mvar (v : expr) (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   set_goals [v],
   target >>= instantiate_mvars >>= tactic.change,
   tac, done,
   set_goals gs

/-- transforms a goal of the form `f x ≼ f y` into `x ≤ y` using lemmas
    marked as `monotonic`.

    Special care is taken when `f` is the repeated application of an
    associative operator and if the operator is commutative
-/
meta def monotonicity1 (cfg : monotonicity_cfg := { monotonicity_cfg . })
: tactic unit :=
hide_meta_vars $ λ asms,
do (l,r,id_rs,g) ← target >>= instantiate_mvars >>= monotonicity_goal cfg <|> fail "monotonic context not found",
   ns ← attribute.get_instances `monotonic,
   p ← mk_pattern g,
   rules ← find_rule asms ns p <|> fail "no applicable rules found",
   when (rules = []) (fail "no applicable rules found"),
   err ← format.join <$> mmap side_conditions rules,
   focus1 $ any_of rules (λ rule, do
     t₀ ← mk_meta_var `(Prop),
     v₀ ← mk_meta_var t₀,
     t₁ ← mk_meta_var `(Prop),
     v₁ ← mk_meta_var t₁,
     tactic.refine $ ``(apply_rel %%(g.rel_def) %%l %%r %%rule %%v₀ %%v₁),
     solve_mvar v₀ (try (any_of id_rs rewrite_target) >>
             ( done <|>
               refl <|>
               ac_refl <|>
               `[simp only [is_associative.assoc]]) ),
     solve_mvar v₁ (try (any_of id_rs rewrite_target) >>
             ( done <|>
               refl <|>
               ac_refl <|>
               `[simp only [is_associative.assoc]]) ),
     n ← num_goals,
     iterate_exactly (n-1) (try $ solve1 $ apply_instance <|> solve_by_elim (some asms)))

meta def monotonicity_n (n : ℕ) (cfg : monotonicity_cfg := { monotonicity_cfg . })
: tactic unit :=
iterate_exactly n (monotonicity1 cfg)

open sum nat

/-- (repeat_until_or_at_most n t u): repeat tactic `t` at most n times or until u succeeds -/
meta def repeat_until_or_at_most : nat → tactic unit → tactic unit → tactic unit
| 0        t _ := fail "too many applications"
| (succ n) t u := u <|> (t >> repeat_until_or_at_most n t u)

meta def repeat_until : tactic unit → tactic unit → tactic unit :=
repeat_until_or_at_most 100000

meta def assert_or_rule : lean.parser (pexpr ⊕ pexpr) :=
(inl <$> texpr <|> (tk ":" *> inr <$> texpr))

/-- `monotonicity` repeatedly unwraps monotonic functions using `monotonicity1`
    until it cannot unwrap anymore.

    `monotonicity h` unwraps monotonic functions until it can use `h` to solve
    the remaining goal. Fails if `h` can never solve the goal.

    `monotonicty : p` asserts `p` and uses it to discharge the final goal after
    unwrapping a series of monotonic functions. Useful for controlling the number
    of unwrappings performed.

    TODO: with `monotonicity h` and `monotonicty : p` split the remaining gaol if
      the provided rule does not solve it completely.
-/
meta def monotonicity : parse assert_or_rule? → tactic unit
 | none := repeat monotonicity1
 | (some (inl h)) :=
do repeat_until monotonicity1 $ (tactic.refine h)
 | (some (inr t)) :=
do h ← i_to_expr t >>= assert `h,
   tactic.swap,
   repeat_until monotonicity1 (tactic.refine $ to_pexpr h)

meta def match_imp : expr → tactic (expr × expr)
 | `(%%e₀ → %%e₁) :=
   do guard (¬ e₁.has_var),
      return (e₀,e₁)
 | _ := failed

meta def monotoncity.check_rel (xs : list expr) (l r : expr) : tactic unit :=
do (_,x,y,_) ← find_one_difference { monotonicity_cfg . }
               l.get_app_args r.get_app_args,
   when (¬ l.get_app_fn = r.get_app_fn)
     (fail format!"{l} and {r} should be the f x and f y for some f"),
   t ← infer_type (list.ilast xs),
   (l',r') ← last_two t.get_app_args
     <|> match_imp t
     <|> fail format!"expecting assumption {t} to be a relation R x y",
   when (¬ x.is_local_constant) (fail format!"expecting a bound variable: {x}"),
   when (¬ y.is_local_constant) (fail format!"expecting a bound variable: {y}"),
   when ([l',r'] ≠ [x,y] ∧ [l',r'] ≠ [y,x])
     (fail "assumption {t} should be relating variables {l'} and {r'}"),
   return ()

meta def monotoncity.check_imp (x₀ : expr) : list expr → tactic unit
| (x₁ :: xs) := infer_type x₁ >>= monotoncity.check_rel xs.reverse x₀
| _ := fail "monotoncity.check_imp"

meta def monotoncity.check (lm_n : name) (prio : ℕ) (persistent : bool) : tactic unit :=
do lm ← mk_const lm_n,
   lm_t ← infer_type lm,
   (xs,h) ← mk_local_pis lm_t,
   x ← try_core (monotoncity.check_imp h xs.reverse),
   match x with
    | (some x) :=
      (do (l,r) ← last_two h.get_app_args,
          monotoncity.check_rel xs l r) <|> return x
    | none :=
      do (l,r) ← last_two h.get_app_args <|> fail format!"expecting: R x y\nactual: {h}",
         monotoncity.check_rel xs l r
   end

@[user_attribute]
meta def monotonicity.attr : user_attribute :=
{ name  := `monotonic
, descr := "monotonicity of functions wrt relations: R₀ x y → R₁ (f x) (f y)"
, after_set := some monotoncity.check  }

end tactic.interactive

variables {α : Type*}

@[monotonic]
lemma add_mono {x y z : α} [ordered_semiring α]
  (h : x ≤ y)
: x + z ≤ y + z :=
add_le_add_right h _

@[monotonic]
lemma sub_mono_left {x y z : α} [ordered_comm_group α]
  (h : x ≤ y)
: x - z ≤ y - z :=
sub_le_sub_right h _

@[monotonic]
lemma sub_mono_right {x y z : α} [ordered_comm_group α]
  (h : y ≤ x)
: z - x ≤ z - y :=
sub_le_sub_left h _

@[monotonic]
lemma mul_mono_nonneg {x y z : α} [ordered_semiring α]
  (h' : 0 ≤ z)
  (h : x ≤ y)
: x * z ≤ y * z :=
by apply mul_le_mul_of_nonneg_right ; assumption

lemma gt_of_mul_lt_mul_neg_right {a b c : α}  [linear_ordered_ring α]
  (h : a * c < b * c) (hc : c ≤ 0) : a > b :=
have nhc : -c ≥ 0, from neg_nonneg_of_nonpos hc,
have h2 : -(b * c) < -(a * c), from neg_lt_neg h,
have h3 : b * (-c) < a * (-c), from calc
     b * (-c) = - (b * c)    : by rewrite neg_mul_eq_mul_neg
          ... < - (a * c)    : h2
          ... = a * (-c)     : by rewrite neg_mul_eq_mul_neg,
lt_of_mul_lt_mul_right h3 nhc

@[monotonic]
lemma mul_mono_nonpos {x y z : α} [linear_ordered_ring α]
  [decidable_rel ((≤) : α → α → Prop)]
  (h' : 0 ≥ z)
  (h : y ≤ x)
: x * z ≤ y * z :=
begin
  by_contradiction h'',
  revert h,
  apply not_le_of_lt,
  apply gt_of_mul_lt_mul_neg_right _ h',
  apply lt_of_not_ge h'',
end

@[monotonic]
lemma sub_mono_left_strict {x y z : α} [ordered_comm_group α]
  (h : x < y)
: x - z < y - z :=
sub_lt_sub_right h _

@[monotonic]
lemma sub_mono_right_strict {x y z : α} [ordered_comm_group α]
  (h : y < x)
: z - x < z - y :=
sub_lt_sub_left h _

@[monotonic]
lemma add_mono_strict {x y z : α} [ordered_semiring α]
  (h : x < y)
: x + z < y + z :=
add_lt_add_right h _

@[monotonic]
lemma nat.sub_mono_left_strict {x y z : ℕ}
  (h' : z ≤ x)
  (h : x < y)
: x - z < y - z :=
begin
  have : z ≤ y,
  { transitivity, assumption, apply le_of_lt h, },
  apply @lt_of_add_lt_add_left _ _ z,
  rw [nat.add_sub_of_le,nat.add_sub_of_le]
  ; solve_by_elim,
end

@[monotonic]
lemma nat.sub_mono_right_strict {x y z : ℕ}
  (h' : x ≤ z)
  (h : y < x)
: z - x < z - y :=
begin
  have h'' : y ≤ z,
  { transitivity, apply le_of_lt h, assumption },
  apply @lt_of_add_lt_add_right _ _ _ x,
  rw [nat.sub_add_cancel h'],
  apply @lt_of_le_of_lt _ _ _ (z - y + y),
  rw [nat.sub_add_cancel h''],
  monotonicity h,
end

attribute [monotonic] or.imp_left
attribute [monotonic] and.imp_right
