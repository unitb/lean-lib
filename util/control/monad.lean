

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

end monad
