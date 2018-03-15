
import util.meta.tactic

open tactic

section
variables x y z : ℕ
include x y z

example : ℕ :=
begin
  clear_except x,
  (do xs ← tactic.local_context, x ← get_local `x, assert (xs = [x]), return ()),
  exact x
end
end

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
begin
  apply_assumption,
  apply_assumption,
end

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
by solve_by_elim

example {α : Type} {p : α → Prop} (h₀ : ∀ x, p x) (y : α) : p y :=
begin
  apply_assumption,
end

example : (∃ x : ℕ, x = 7) :=
begin
  one_point, refl,
end

example (p : Prop) : (∃ x : ℕ, x = 7) ∨ p :=
begin
  one_point, left, refl,
end

example (p q : ℕ → Prop) : (∃ x : ℕ, (x = 7 ∧ q x) ∧ p x) ∨ p 1 :=
begin
  one_point,
  guard_target (7 = 7 ∧ q 7) ∧ p 7 ∨ p 1,
  admit
end

example (p q : ℕ → Prop) : (∃ x : ℕ, (p x ∧ x = 7 ∧ q x) ∧ p x) ∨ p 1 :=
begin
  one_point,
  guard_target (p 7 ∧ 7 = 7 ∧ q 7) ∧ p 7 ∨ p 1,
  admit
end

example {x y : ℕ}
: x = 1 → false :=
begin
  intros a,
  wlog : x = y using x y,
  guard_target x = y ∨ y = x, admit,
  guard_hyp a := x = y,
  guard_hyp a_1 := x = 1, admit,
end
