
import data.dlist

import util.logic
import util.data.traversable
import util.control.monad

import util.data.list

variables {a b c p : Prop}

namespace tactic.interactive

open lean lean.parser  interactive
open interactive.types -- expr
open tactic

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def match_exists : expr → tactic (name × expr × expr)
 | `(@Exists _ %%e) := return (expr.binding_name e
                           ,expr.binding_domain e
                           ,expr.binding_body e)
 | _ := fail "expecting an existential"

meta def match_forall : expr → tactic (name × expr × expr)
 | (expr.pi n _ d b) := return (n,d,b)
 | e := fail $ format! "expecting a universal {e}"

/-- for goals of the form `f x → f x'` for certain monotonic or antimonotonic f,
    bring the context of `x` into the assumptions.
    Possible f are
      (∃ x, _)
      (∀ x, _)
      →, ∧, ∨, ¬
    TODO: add monotonicity type class
-/
meta def intro_mono (id : parse ident_ ?) : tactic unit :=
do g ← target >>= instantiate_mvars,
   match g with
    | `( (∃ x : %%t₀, %%e₀) → (∃ x : %%t₁, %%e₁) ) :=
      do (is_def_eq t₀ t₁
            <|> fail (format! "type of bound variables don't match: {t₀} ≠ {t₁}")),
         `[apply exists_imp_exists],
         intro id
    | `( (∀ x : %%t₀, %%e₀) → (∀ x : %%t₁, %%e₁) ) :=
        (do is_def_eq t₀ t₁,
            `[apply forall_imp_forall _],
            intro id)
    <|> (do (guard (¬ e₀.has_var ∧ ¬ e₁.has_var)
                   <|> fail (format! "type of bound variables don't match: {t₀} ≠ {t₁}")),
            is_def_eq e₀ e₁,
            p ← to_expr ``(%%t₁ → %%t₀),
            assert `h p,
            swap,
            `[intros h₀ h₁, apply h₀, apply h h₁])
    | `( (%%t₀ ∧ %%e₀) → (%%t₁ ∧ %%e₁) ) :=
        (do is_def_eq t₀ t₁,
            `[apply and.mono_right],
            intro id)
    <|> (do is_def_eq e₀ e₁,
            `[apply and.mono_left],
            intro id)
    | `( (%%t₀ ∨ %%e₀) → (%%t₁ ∨ %%e₁) ) :=
        (do is_def_eq t₀ t₁,
            `[apply classical.or.mono_right],
            intro id)
    <|> (do is_def_eq e₀ e₁,
            `[apply classical.or.mono_left],
            intro id)
    | `( (¬ %%e₀) → (¬ %%e₁) ) :=
        (`[apply mt])
    | _ := fail "cannot apply monotonicity rules to goal"
   end

meta def intros_mono_dep : tactic unit :=
do g ← target,
   match g with
    | `(%%e₀ → %%e₁) :=
        (do (n₀,t₀,e₀) ← match_exists e₀,
            (n₁,t₁,e₁) ← match_exists e₁,
            if e₀.has_var_idx 0 then intro_mono (some n₀) >> intros_mono_dep
            else if e₁.has_var_idx 0 then intro_mono (some n₁) >> intros_mono_dep
            else return ())
    <|> (do (n₀,t₀,e₀) ← match_forall e₀,
            (n₁,t₁,e₁) ← match_forall e₁,
            if e₀.has_var_idx 0 then intro_mono (some n₀) >> intros_mono_dep
            else if e₁.has_var_idx 0 then intro_mono (some n₁) >> intros_mono_dep
            else return ())
    <|> (do expr.is_not e₀,
            expr.is_not e₁,
            intro_mono none >> intros_mono_dep)
    <|> return ()
    | _ := fail "expecting an implication"
   end

meta def introv_mono : parse ident_ * → tactic unit
 | [] := intros_mono_dep
 | (x::xs) := intros_mono_dep >> intro_mono (some x) >> introv_mono xs

meta def intros_mono : parse ident_ * → tactic unit
 | [] := repeat (intro_mono none)
 | xs := mmap' (intro_mono ∘ some) xs

example {α β : Type} (p q : α → β → Prop) (r : α → Prop) (s : β → Prop)
  (h : ∀ x y, r x → ¬ s y → q x y → p x y)
: (∃ x, ∀ y, r x ∧ (¬ p x y ∨ s y))
→ (∃ i, ∀ j, r i ∧ (¬ q i j ∨ s j)) :=
begin
  intro_mono k,
  intro_mono z,
  intro_mono i,
  intro_mono j,
  intro_mono ,
  apply h ; assumption
end

example {α β : Type} (p q : α → β → Prop) (r : α → Prop) (s : β → Prop)
  (h : ∀ x y, r x → ¬ s y → q x y → p x y)
: (∃ x, ∀ y, r x ∧ (¬ p x y ∨ s y))
→ (∃ i, ∀ j, r i ∧ (¬ q i j ∨ s j)) :=
begin
  intros_mono,
  apply h ; assumption
end

example {α β : Type} (p q : α → β → Prop) (r : α → Prop) (s : β → Prop)
  (h : ∀ x y, r x → ¬ s y → q x y → p x y)
: (∃ x, ∀ y, r x ∧ (¬ p x y ∨ s y))
→ (∃ i, ∀ j, r i ∧ (¬ q i j ∨ s j)) :=
begin
  intros_mono,
  apply h ; assumption,
end

example {α β : Type} (p : α → β → Prop) (r : α → Prop) (s : β → Prop)
  (h : ∀ x y, r x → ¬ r x → p x y → r x)
: (∃ x, ∀ y : β, r x ∧ (¬ r x ∨ r x))
→ (∃ i, ∀ j, r i ∧ (¬ p i j ∨ r i)) :=
begin
  introv_mono h₀ h₁,
  apply h ; assumption,
end

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

-- meta instance : has_reflect mono_function :=
-- by mk_has_reflect_instance

meta def parse_imp' : list expr → expr → tactic (expr × list expr)
 | xs e :=
   do `(%%e₀ → %%e₁) ← return e | return (e,xs),
      if (¬ e₁.has_var) then
        parse_imp' (e₀ :: xs) e₁
      else
        return (e,xs)

meta def parse_imp := parse_imp' []

@[user_attribute]
meta def monotonicity.attr : user_attribute :=
{ name  := `monotonic
, descr := "monotonicity of functions wrt relations: R₀ x y → R₁ (f x) (f y)" }

open list has_map

meta def is_mvar : expr → bool
 | (expr.mvar _ _ _) := tt
 | _ := ff

meta def compare (unif : bool) (e₀ e₁ : expr) : tactic unit := do
if unif then do
guard (¬ is_mvar e₀ ∧ ¬ is_mvar e₁),
unify e₀ e₁
else is_def_eq e₀ e₁

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

meta class elaborable (α : Type) (β : inout Type) :=
  (elaborate : α → tactic β)

export elaborable (elaborate)

meta instance : elaborable pexpr expr :=
⟨ to_expr ⟩

meta instance elaborable_list {α α'} [elaborable α α'] : elaborable (list α) (list α') :=
⟨ mmap (elaborate _) ⟩

meta def mono_function.elaborate : mono_function ff → tactic mono_function
| (mono_function.non_assoc x y z) :=
mono_function.non_assoc <$> elaborate _ x
                        <*> elaborate _ y
                        <*> elaborate _ z
| (mono_function.assoc x y z) :=
mono_function.assoc <$> elaborate _ x
                    <*> traverse (elaborate _) y
                    <*> traverse (elaborate _) z
| (mono_function.assoc_comm x y) :=
mono_function.assoc_comm <$> elaborate _ x
                         <*> elaborate _ y


meta instance elaborable_mono_function : elaborable (mono_function ff) mono_function :=
⟨ mono_function.elaborate ⟩

meta instance prod_elaborable {α α' β β' : Type} [elaborable α α']  [elaborable β β']
: elaborable (α × β) (α' × β') :=
⟨ λ i, prod.rec_on i (λ x y, prod.mk <$> elaborate _ x <*> elaborate _ y) ⟩

run_cmd
do xs ← mmap to_expr [``(1),``(2),``(3)],
   ys ← mmap to_expr [``(1),``(2),``(4)],
   x ← match_prefix ff xs ys,
   p ← elaborate _ ([``(1),``(2)] , [``(3)], [``(4)]),
   guard $ x = p

/--
`(prefix,left,right,suffix) ← match_assoc unif l r` finds the
longest prefix and suffix common to `l` and `r` and
returns them along with the differences  -/
meta def match_assoc (unif : bool) (l : list expr) (r : list expr)
: tactic (list expr × list expr × list expr × list expr) :=
do (pre,l₁,r₁) ← match_prefix unif l r,
   (suf,l₂,r₂) ← match_prefix unif (reverse l₁) (reverse r₁),
   return (pre,reverse l₂,reverse r₂,reverse suf)

run_cmd
do xs ← mmap to_expr [``(1),``(2),``(3),``(6),``(7)],
   ys ← mmap to_expr [``(1),``(2),``(4),``(5),``(6),``(7)],
   x ← match_assoc ff xs ys,
   p ← elaborate _ ([``(1), ``(2)], [``(3)], ([``(4), ``(5)], [``(6), ``(7)])),
   guard (x = p)

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

run_cmd
do x ← to_expr ``(7 + 3 : ℕ) >>= check_ac,
   x ← pp x.2.2.1,
   guard $ x.to_string = "(some (add_monoid_to_is_left_id, 0))"

open dlist has_map

meta def parse_assoc_chain' (f : expr) : expr → tactic (dlist expr)
 | e :=
 (do (expr.app (expr.app f' x) y) ← return e,
     is_def_eq f f',
     (++) <$> parse_assoc_chain' x <*> parse_assoc_chain' y)
<|> return (singleton e)

meta def parse_assoc_chain (f : expr) : expr → tactic (list expr) :=
map dlist.to_list ∘ parse_assoc_chain' f

open monad (mmap₂')

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

run_cmd
do parse_mono_function' ``(1 + 3 + 2 + 6) ``(4 + 2 + 1 + 5) >>= trace,
   parse_mono_function' ``([1] ++ [3] ++ [2] ++ [6]) ``([4] ++ [2] ++ ([1] ++ [5]))
     >>= trace,
   parse_mono_function' ``([1] ++ [3] ++ [2] ++ [2]) ``([1] ++ [5] ++ ([4] ++ [2]))
     >>= trace

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

private meta def match_head (p : expr) : expr → expr → tactic expr
 | e t :=
(unify t p >> instantiate_mvars e)
<|>
do (expr.pi _ _ d b) ← return t | failed,
   v ← mk_meta_var d,
   match_head (expr.app e v) (b.instantiate_var v)

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

-- meta def mk_associative_pattern : option expr → option expr → expr := _

meta def match_rule (pat : expr) (r : name) : tactic expr :=
do  r' ← mk_const r,
    t  ← infer_type r',
    match_head pat r' t

meta def find_lemma (pat : expr) : list name → tactic expr
 | [] := failed
 | (r :: rs) :=
 do match_rule pat r <|> find_lemma rs

meta def match_chaining_rules (ls : list name) (x₀ x₁ : expr) : tactic expr :=
do x' ← to_expr ``(%%x₁ → %%x₀),
   r₀ ← find_lemma x' ls,
   r₁ ← find_lemma x₁ ls,
   return (expr.app r₀ r₁)

meta def find_rule (ls : list name) : mono_law → tactic (expr)
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

meta def monotonicity1 : tactic unit :=
do (l,r,g) ← target >>= instantiate_mvars >>= monotonicity_goal,
   ns ← attribute.get_instances `monotonic,
   p ← mk_pattern g,
   rule ← find_rule ns p,
   x ← to_expr ``(apply_rel %%(g.rel_def) %%l %%r %%rule),
   tactic.apply x,
   solve1 (refl <|> ac_refl <|> `[simp only [is_associative.assoc]]),
   solve1 (refl <|> ac_refl <|> `[simp only [is_associative.assoc]])

@[monotonic]
lemma add_mono {α : Type} {x y z : α} [ordered_semiring α]
  (h : x ≤ y)
: x + z ≤ y + z :=
add_le_add_right h _

@[monotonic]
lemma sub_mono_left {α : Type} {x y z : α} [ordered_comm_group α]
  (h : x ≤ y)
: x - z ≤ y - z :=
sub_le_sub_right h _

@[monotonic]
lemma sub_mono_right {α : Type} {x y z : α} [ordered_comm_group α]
  (h : y ≤ x)
: z - x ≤ z - y :=
sub_le_sub_left h _

lemma bar
  (h : 3 + 6 ≤ 4 + 5)
: 1 + 3 + 2 + 6 ≤ 4 + 2 + 1 + 5 :=
begin
  monotonicity1,
  apply h
end

lemma bar'
  (h : 3 ≤ (4 : ℤ))
  (h' : 5 ≤ (6 : ℤ))
: (1 + 3 + 2) - 6 ≤ (4 + 2 + 1 : ℤ) - 5 :=
begin
  transitivity (1 + 3 + 2 - 5 : ℤ),
  monotonicity1,
  apply h',
  monotonicity1,
  monotonicity1,
  apply h
end

@[simp]
def list.le {α : Type*} [has_le α] : list α → list α → Prop
 | (x::xs) (y::ys) := x ≤ y ∧ list.le xs ys
 | [] [] := true
 | _ _ := false

@[simp]
instance {α : Type*} [has_le α] : has_le (list α) :=
⟨ list.le ⟩

@[refl]
lemma list.le_refl {α : Type*} [preorder α] {xs : list α}
: xs ≤ xs :=
begin
  induction xs with x xs,
  { trivial },
  { simp [has_le.le,list.le],
    split, apply le_refl, apply ih_1 }
end

@[trans]
lemma list.le_trans {α : Type*} [preorder α]
  {xs zs : list α} (ys : list α)
  (h  : xs ≤ ys)
  (h' : ys ≤ zs)
: xs ≤ zs :=
begin
  revert ys zs,
  induction xs with x xs
  ; intros ys zs h h'
  ; cases ys with y ys
  ; cases zs with z zs
  ; try { cases h ; cases h' ; done },
  { refl },
  { simp [has_le.le,list.le],
    split,
    apply le_trans h.left h'.left,
    apply ih_1 _ h.right h'.right, }
end

@[monotonic]
lemma list_le_mono_left {α : Type*} [preorder α] {xs ys zs : list α}
  (h : xs ≤ ys)
: xs ++ zs ≤ ys ++ zs :=
begin
  revert ys,
  induction xs with x xs ; intros ys h,
  { cases ys, refl, cases h },
  { cases ys with y ys, cases h, simp [has_le.le,list.le] at *,
    revert h, apply and.imp_right,
    apply ih_1 }
end

@[monotonic]
lemma list_le_mono_right {α : Type*} [preorder α] {xs ys zs : list α}
  (h : xs ≤ ys)
: zs ++ xs ≤ zs ++ ys :=
begin
  revert ys zs,
  induction xs with x xs ; intros ys zs h,
  { cases ys, { simp }, cases h  },
  { cases ys with y ys, cases h, simp [has_le.le,list.le] at *,
    rw [list.append_cons _ x,list.append_cons _ y],
    apply list.le_trans (zs ++ [y] ++ xs),
    { apply list_le_mono_left,
      induction zs with z zs,
      { simp [has_le.le,list.le], apply h.left },
      { simp [has_le.le,list.le], split, apply le_refl,
        apply ih_1_1, } },
    { apply ih_1 h.right, } }
end

lemma bar_bar'
  (h : [] ++ [3] ++ [2] ≤ [1] ++ [5] ++ [4])
: [] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
begin
  monotonicity1,
  apply h
end

lemma bar_bar''
  (h : [3] ++ [2] ++ [2] ≤ [5] ++ [4] ++ [])
: [1] ++ ([3] ++ [2]) ++ [2] ≤ [1] ++ [5] ++ ([4] ++ []) :=
begin
  monotonicity1,
  apply h,
end

lemma bar_bar
  (h : [3] ++ [2] ≤ [5] ++ [4])
: [1] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
begin
  monotonicity1,
  apply h
end

def P (x : ℕ) := 7 ≤ x
def Q (x : ℕ) := x ≤ 7

@[monotonic]
lemma P_mono {x y : ℕ}
  (h : x ≤ y)
: P x → P y :=
by { intro h', apply le_trans h' h }

@[monotonic]
lemma Q_mono {x y : ℕ}
  (h : y ≤ x)
: Q x → Q y :=
by apply le_trans h

example (x y z : ℕ)
  (h : x ≤ y)
: P (x + z) → P (z + y) :=
begin
  monotonicity1,
  monotonicity1,
  apply h,
end

example (x y z : ℕ)
  (h : y ≤ x)
: Q (x + z) → Q (z + y) :=
begin
  monotonicity1,
  monotonicity1,
  apply h,
end

end tactic.interactive
