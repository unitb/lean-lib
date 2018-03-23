
universes u v

namespace state_t

variables {σ α : Type u}
variables {m : Type u → Type u}
variables [monad m]
variables [is_lawful_monad m]

open is_lawful_monad
lemma get_bind (s : σ) (f : σ → state_t σ m α)
: (get >>= f).run s = (f s).run s :=
by { simp [bind,state_t.bind,get,state_t.get,monad_state.lift,pure_bind,has_pure.pure,bind._match_1] }

end state_t
