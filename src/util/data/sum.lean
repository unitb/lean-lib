
universe variables u v u' v'

namespace sum

variables {α : Type u}   {β : Type v}
          {α' : Type u'} {β' : Type v'}

def is_left : α ⊕ β → bool
  | (sum.inl _) := tt
  | (sum.inr _) := ff

def is_right : α ⊕ β → bool
  | (sum.inl _) := ff
  | (sum.inr _) := tt

instance {α : Type u} : functor (sum α) :=
 { map := λ β γ f x, sum.rec_on x sum.inl (sum.inr ∘ f) }

def bimap (f : α → α') (g : β → β') : α ⊕ β → α' ⊕ β'
 | (inl x) := inl $ f x
 | (inr x) := inr $ g x

def swap : α ⊕ β → β ⊕ α
 | (inl x) := inr x
 | (inr x) := inl x

end sum
