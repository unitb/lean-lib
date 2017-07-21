
universe variables u v

variables {α : Type u}

@[simp]
lemma coe_subtype_eq_self {x : α} {P : α → Prop}
  (h : P x)
: ↑ (⟨x, h⟩ : subtype P) = x :=
rfl
