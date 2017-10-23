
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
  xassumption,
  xassumption,
end

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
by auto

example {α : Type} {p : α → Prop} (h₀ : ∀ x, p x) (y : α) : p y :=
begin
  xassumption,
end
