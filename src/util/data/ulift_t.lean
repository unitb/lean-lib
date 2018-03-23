
import util.data.functor

universes u v w

namespace ulift

variables {α β γ : Type u}

def pure (x : α) : ulift α := ⟨ x ⟩

def bind (x : ulift α) (f : α → ulift β) : ulift β :=
f (down x)

instance : has_bind ulift := ⟨ @bind ⟩

lemma bind_assoc (x : ulift α) (f : α → ulift β) (g : β → ulift γ)
: x >>= f >>= g = x >>= (λ i, f i >>= g) :=
by { cases x ; refl }

lemma pure_bind (x : α) (f : α → ulift β)
: pure x >>= f = f x := sorry

lemma id_map (x : ulift α)
: ulift.bind x (ulift.pure ∘ id) = x := sorry

end ulift

instance : monad ulift :=
{ bind := @ulift.bind
, pure := @ulift.pure }

instance : is_lawful_monad ulift :=
{ pure_bind := @ulift.pure_bind
, bind_assoc := @ulift.bind_assoc
, id_map := @ulift.id_map }

variables (m : Type (max w u) → Type v)

structure ulift_t (α : Type w) :=
(run : m (ulift α))

namespace ulift_t

export ulift (up down up_down)

variables {m}

variables {α β γ : Type w}

protected def bind [has_bind m] (x : ulift_t m α) (f : α → ulift_t m β) : ulift_t m β :=
⟨ x.run >>= ulift_t.run ∘ f ∘ down ⟩

protected def pure [has_pure m] (x : α) : ulift_t m α :=
⟨ pure (up x) ⟩

instance [has_bind m] : has_bind (ulift_t m) :=
⟨ λ α β, @ulift_t.bind m α β _ ⟩

instance [has_pure m] : has_pure (ulift_t m) :=
⟨ λ α, @ulift_t.pure m α _ ⟩

variables [monad m] [is_lawful_monad m]
open is_lawful_monad

lemma bind_assoc (x : ulift_t m α) (f : α → ulift_t m β) (g : β → ulift_t m γ)
: x >>= f >>= g = x >>= (λ i, f i >>= g) :=
by simp [has_bind.bind,ulift_t.bind,bind_assoc]

lemma pure_bind (x : α) (f : α → ulift_t m β)
: ulift_t.pure x >>= f = f x :=
begin
  destruct f x, intros y h,
  simp [has_bind.bind,ulift_t.bind,ulift_t.pure],
  simp [pure_bind,function.comp,h],
end

lemma id_map (x : ulift_t m α)
: x >>= pure ∘ id = x :=
begin
  cases x,
  simp [has_bind.bind,ulift_t.bind,function.comp,pure,has_pure.pure,ulift_t.pure],
  simp [up_down],
end

end ulift_t

instance {m : Type (max w u) → Type v} [monad m] : monad (ulift_t m) :=
{ bind := λ α β, ulift_t.bind
, pure := λ α, ulift_t.pure }

instance {m : Type (max w u) → Type v} [monad m] [is_lawful_monad m] : is_lawful_monad (ulift_t m) :=
{ pure_bind := λ α β, @ulift_t.pure_bind m α β _ _
, bind_assoc := λ α β γ, ulift_t.bind_assoc
, id_map := λ α, @ulift_t.id_map m α _ _ }
