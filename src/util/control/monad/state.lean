
universes u v

namespace state_t

variables {σ α : Type u}
variables {m : Type u → Type v}
variables [monad m]

lemma read_bind (s : σ) (f : σ → state_t σ m α)
: (read >>= f) s = f s s :=
by simp [read,bind,state_t_bind,monad.pure_bind]

end state_t
