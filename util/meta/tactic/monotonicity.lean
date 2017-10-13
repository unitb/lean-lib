
import util.logic

variables {a b c p : Prop}

lemma and.mono_right
  (h : a → (b → c))
: a ∧ b → a ∧ c :=
sorry

lemma and.mono_left
  (h : a → (b → c))
: b ∧ a → c ∧ a :=
sorry

lemma or.mono_right
  (h : ¬ a → (b → c))
: a ∨ b → a ∨ c :=
sorry

lemma or.mono_left
  (h : ¬ a → (b → c))
: b ∨ a → c ∨ a :=
sorry

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
            `[apply or.mono_right],
            intro id)
    <|> (do is_def_eq e₀ e₁,
            `[apply or.mono_left],
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

end tactic.interactive
