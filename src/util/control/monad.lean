import util.control.applicative

universes u v

variable {m : Type u → Type v}
variable [monad m]
variables {α β γ : Type u}

open has_map nat

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

open applicative

def monad.mrepeat : ℕ → m α → m (list α)
 | 0 _ := return []
 | (succ n) m := lift₂ (::) m (monad.mrepeat n m)

def monad.mrepeat' : ℕ → m α → m punit
 | 0 _ := return punit.star
 | (succ n) m := m *> monad.mrepeat' n m
