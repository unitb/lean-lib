
import data.dlist

import util.algebra.group
import util.data.list
import util.data.traversable
import util.meta.tactic.basic

variables {a b c p : Prop}

namespace tactic.interactive

open lean lean.parser  interactive
open interactive.types
open tactic

local postfix `?`:9001 := optional
local postfix *:9001 := many

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

meta instance : has_to_tactic_format mono_function :=
{ to_tactic_format := mono_function.to_tactic_format }

meta structure mono_ctx :=
  (to_rel : expr → expr → expr)
  (function : mono_function)
  (left right rel_def : expr)

meta def mono_ctx.to_tactic_format (ctx : mono_ctx) : tactic format :=
do fn  ← pp ctx.function,
   l   ← pp ctx.left,
   r   ← pp ctx.right,
   rel ← pp ctx.rel_def,
   return format!"{{ function := {fn}\n, left  := {l}\n, right := {r}\n, rel_def := {rel} }"

meta instance has_to_tactic_format_mono_ctx : has_to_tactic_format mono_ctx :=
{ to_tactic_format := mono_ctx.to_tactic_format }

meta def as_goal (e : expr) (tac : itactic) : itactic :=
do gs ← get_goals,
   set_goals [e],
   tac,
   set_goals gs

meta def unify_with_instance (e : expr) : tactic unit :=
as_goal e $
apply_instance
<|>
apply_opt_param
<|>
apply_auto_param
<|>
auto
<|>
return ()

private meta def match_head (p : expr)
: list expr → expr → expr → tactic expr
 | vs e t :=
(unify t p >> mmap' unify_with_instance vs.tail >> instantiate_mvars e)
<|>
do (expr.pi _ _ d b) ← return t | failed,
   v ← mk_meta_var d,
   match_head (v::vs) (expr.app e v) (b.instantiate_var v)

meta def pi_head : expr → tactic expr
| (expr.pi n _ t b) :=
do v ← mk_meta_var t,
   pi_head (b.instantiate_var v)
| e := return e

def last_two {α : Type*} : list α → option (α × α)
| [] := none
| [x] := none
| (x₀ :: x₁ :: xs) := last_two (x₁ :: xs) <|> some (x₀, x₁)

meta def is_mvar : expr → bool
 | (expr.mvar _ _ _) := tt
 | _ := ff

meta def compare (unif : bool) (e₀ e₁ : expr) : tactic unit := do
if unif then do
guard (¬ is_mvar e₀ ∧ ¬ is_mvar e₁),
unify e₀ e₁
else is_def_eq e₀ e₁

open list has_map dlist monad (mmap₂')

meta def find_one_difference (unif : bool)
: list expr → list expr → tactic (list expr × expr × expr × list expr)
 | (x :: xs) (y :: ys) :=
   do c ← try_core (compare unif x y),
      if c.is_some
      then prod.map (cons x) id <$> find_one_difference xs ys
      else do
        guard (xs.length = ys.length),
        mmap₂' (compare unif) xs ys,
        return ([],x,y,xs)
 | _ _ := failed

meta def monotoncity.check_rel (xs : list expr) (l r : expr) : tactic unit :=
do (_,x,y,_) ← find_one_difference ff l.get_app_args r.get_app_args <|> fail "bar",
   when (¬ l.get_app_fn = r.get_app_fn)
     (fail format!"{l} and {r} should be the f x and f y for some f"),
   t ← infer_type (list.ilast xs),
   (l',r') ← last_two t.get_app_args
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

meta def delete_expr (unif : bool) (e : expr)
: list expr → tactic (option (list expr))
 | [] := return none
 | (x :: xs) :=
(compare unif e x >> return (some xs))
<|>
(map (cons x) <$> delete_expr xs)

meta def match_ac' (unif : bool)
: list expr → list expr → tactic (list expr × list expr × list expr)
 | es (x :: xs) := do
    es' ← delete_expr unif x es,
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
do (s',l',r') ← match_ac' unif l r,
   s' ← mmap instantiate_mvars s',
   l' ← mmap instantiate_mvars l',
   r' ← mmap instantiate_mvars r',
   return (s',l',r')

meta def match_prefix (unif : bool)
: list expr → list expr → tactic (list expr × list expr × list expr)
| (x :: xs) (y :: ys) :=
  (do compare unif x y,
      prod.map ((::) x) id <$> match_prefix xs ys)
<|> return ([],x :: xs,y :: ys)
| xs ys := return ([],xs,ys)

/--
`(prefix,left,right,suffix) ← match_assoc unif l r` finds the
longest prefix and suffix common to `l` and `r` and
returns them along with the differences  -/
meta def match_assoc (unif : bool) (l : list expr) (r : list expr)
: tactic (list expr × list expr × list expr × list expr) :=
do (pre,l₁,r₁) ← match_prefix unif l r,
   (suf,l₂,r₂) ← match_prefix unif (reverse l₁) (reverse r₁),
   return (pre,reverse l₂,reverse r₂,reverse suf)

meta def check_ac : expr → tactic (bool × bool × option (expr × expr) × expr)
 | (expr.app (expr.app f x) y) :=
   do t ← infer_type x,
      a ← try_core $ to_expr ``(is_associative %%t %%f) >>= mk_instance,
      c ← try_core $ to_expr ``(is_commutative %%t %%f) >>= mk_instance,
      i ← try_core (do
          v ← mk_meta_var t,
          prod.mk <$> (to_expr ``(is_left_id %%t %%f %%v) >>= mk_instance)
                  <*> instantiate_mvars v),
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

meta def fold_assoc (op : expr) : option (expr × expr) → list expr → option expr
| _ (x::xs) := some $ foldl (expr.app ∘ expr.app op) x xs
| none []   := none
| (some (inst,x₀)) [] := some x₀

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
: tactic (expr × expr × mono_function) :=
do (full_f,ls,rs) ← same_function l r,
   (a,c,i,f) ← check_ac l,
   if a
   then if c
   then do
     (s,ls,rs) ← monad.join (match_ac ff
                   <$> parse_assoc_chain f l
                   <*> parse_assoc_chain f r),
     l' ← fold_assoc f i ls,
     r' ← fold_assoc f i rs,
     s' ← fold_assoc1 f s,
     return (l',r',mono_function.assoc_comm f s')
   else do -- a ∧ ¬ c
     (pre,ls,rs,suff) ← monad.join (match_assoc ff
                   <$> parse_assoc_chain f l
                   <*> parse_assoc_chain f r),
     l'   ← fold_assoc f i ls,
     r'   ← fold_assoc f i rs,
     let pre'  := fold_assoc1 f pre,
     let suff' := fold_assoc1 f suff,
     return (l',r',mono_function.assoc f pre' suff')
   else do -- ¬ a
     (xs₀,x₀,x₁,xs₁) ← find_one_difference ff ls rs,
     return (x₀,x₁,mono_function.non_assoc full_f xs₀ xs₁)

meta def parse_mono_function' (l r : pexpr) :=
do l' ← to_expr l,
   r' ← to_expr r,
   parse_mono_function l' r'

meta def monotonicity_goal : expr → tactic (expr × expr × mono_ctx)
 | `(%%e₀ → %%e₁) :=
  do (l,r,f) ← parse_mono_function e₀ e₁,
     t₀ ← infer_type e₀,
     t₁ ← infer_type e₁,
     rel_def ← to_expr ``(λ x₀ x₁, (x₀ : %%t₀) → (x₁ : %%t₁)),
     return (e₀, e₁,
            { function := f
            , left := l, right := r
            , to_rel := expr.pi `x binder_info.default
            , rel_def := rel_def })
 | (expr.app (expr.app rel e₀) e₁) :=
  do (l,r,f) ← parse_mono_function e₀ e₁,
     return (e₀, e₁,
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
 | assoc : expr × expr → expr × expr → mono_law
 | other : expr → mono_law

meta def mono_law.to_tactic_format : mono_law → tactic format
 | (mono_law.other e) := do e ← pp e, return format!"other {e}"
 | (mono_law.assoc (x₀,x₁) (y₀,y₁)) :=
do x₀ ← pp x₀,
   x₁ ← pp x₁,
   y₀ ← pp y₀,
   y₁ ← pp y₁,
   return format!"assoc {x₀}; {x₁} | {y₀}; {y₁}"

meta instance has_to_tactic_format_mono_law : has_to_tactic_format mono_law :=
{ to_tactic_format := mono_law.to_tactic_format }

meta def mk_rel (ctx : mono_ctx) (f : expr → expr) : expr :=
ctx.to_rel (f ctx.left) (f ctx.right)

meta def mk_pattern (ctx : mono_ctx) : option mono_law :=
match ctx.function with
 | (mono_function.assoc f (some x) (some y)) :=
   mono_law.assoc
       ( mk_rel ctx (λ i, bin_op f x (bin_op f i y))
       , mk_rel ctx (λ i, bin_op f i y))
       ( mk_rel ctx (λ i, bin_op f (bin_op f x i) y)
       , mk_rel ctx (λ i, bin_op f x i))
 | (mono_function.assoc f (some x) none) :=
   mono_law.other $
   ctx.to_rel (mk_fun_app ctx.function ctx.left)
              (mk_fun_app ctx.function ctx.right)
 | (mono_function.assoc f none (some y)) :=
   mono_law.other $
   ctx.to_rel (mk_fun_app ctx.function ctx.left)
              (mk_fun_app ctx.function ctx.right)
 | (mono_function.assoc f none none) :=
   none
 | _ :=
   mono_law.other $
   ctx.to_rel (mk_fun_app ctx.function ctx.left)
              (mk_fun_app ctx.function ctx.right)
end

meta def match_rule (pat : expr) (r : name) : tactic expr :=
do  r' ← mk_const r,
    t  ← infer_type r',
    match_head pat [] r' t

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
 | (mono_law.other p) := find_lemma p ls

meta def list_meta_vars (e : expr) : list expr :=
e.fold [] (λ e' _ es, if is_mvar e' then e' :: es else es)

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
do let vs := list_meta_vars e,
   ts ← mmap one_line vs.tail,
   let r := e.get_app_fn.const_name,
   return format!"{r}:\n{format.join ts}"

meta def monotonicity1 : tactic unit :=
do (l,r,g) ← target >>= instantiate_mvars >>= monotonicity_goal,
   ns ← attribute.get_instances `monotonic,
   p ← mk_pattern g,
   rules ← find_rule ns p <|> fail "no applicable rules found",
   when (rules = []) (fail "no applicable rules found"),
   err ← format.join <$> mmap side_conditions rules,
   focus1 $ any_of rules (λ rule, do
     x ← to_expr ``(apply_rel %%(g.rel_def) %%l %%r %%rule),
     tactic.apply x,
     solve1 (refl <|> ac_refl <|> `[simp only [is_associative.assoc]]),
     solve1 (refl <|> ac_refl <|> `[simp only [is_associative.assoc]]),
     n ← num_goals,
     repeat_exactly (n-1) (solve1 $ apply_instance <|> auto))
   <|> fail (to_fmt "Side condition for rules cannot be proved: \n" ++ err)

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
