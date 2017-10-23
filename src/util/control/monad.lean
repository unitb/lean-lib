

universes u v

variable {m : Type u → Type v}
variable [monad m]
variables {α β γ : Type u}

open has_map

namespace monad

lemma map_bind (f : γ → β) (x : m α) (g : α → m γ)
: f <$> (x >>= g) = x >>= (map f ∘ g) :=
sorry

lemma bind_map (f : α → β) (x : m α) (g : β → m γ)
: f <$> x >>= g = x >>= g ∘ f :=
sorry

def mmap₂  (f : α → β → m γ) : list α → list β → m (list γ)
| (x :: xs) (y :: ys) := (::) <$> f x y <*> mmap₂ xs ys
| [] _ := pure []
| _ [] := pure []

def mmap₂'  (f : α → β → m γ) : list α → list β → m punit
| (x :: xs) (y :: ys) := f x y *> mmap₂' xs ys
| [] _ := pure punit.star
| _ [] := pure punit.star

end monad
