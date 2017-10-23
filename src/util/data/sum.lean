
universe variables u v

namespace sum

variables {α : Type u} {β : Type v}

def is_left : α ⊕ β → bool
  | (sum.inl _) := tt
  | (sum.inr _) := ff

def is_right : α ⊕ β → bool
  | (sum.inl _) := ff
  | (sum.inr _) := tt

instance {α : Type u} : has_map (sum α) :=
 { map := λ β γ f x, sum.rec_on x sum.inl (sum.inr ∘ f) }

end sum
