
universe variables u v u'

section thms

variables {F : Type u → Type v}
variables {α β γ : Type u}
variables [functor F]

lemma functor.id_map' : fmap id = (id : F α → F α) :=
by { apply funext, apply functor.id_map }

lemma functor.map_comp' (f : α → β) (g : β → γ)
: fmap (g ∘ f) = (fmap g ∘ fmap f : F α → F γ) :=
by { apply funext, intro, apply functor.map_comp }

end thms

/- identity functor -/

structure identity (α : Type u) : Type u :=
  (run_identity : α)

namespace identity

open function

variables {α : Type u} {β : Type v} {γ : Type u'}

def map (f : α → β) : identity α → identity β
  | ⟨ x ⟩ := ⟨ f x ⟩

local infixr <$> := map

lemma id_map : ∀ (x : identity α), map id x = x
 | ⟨ x ⟩ := rfl

lemma map_comp (f : α → β) (g : β → γ)
: ∀ (x : identity α), map (g ∘ f) x = g <$> f <$> x
 | ⟨ x ⟩ := rfl

end identity

instance : functor identity :=
{ map := @identity.map
, id_map := @identity.id_map
, map_comp := @identity.map_comp }

lemma identity.fmap_mk {α β : Type v}  (f : α → β) (x : α)
: f <$> identity.mk x = identity.mk (f x) := rfl

/- compose functor instance -/

structure compose (f : Type u → Type u') (g : Type v → Type u) (α : Type v) : Type u' :=
  (run_compose : f $ g α)

namespace compose

variables {f : Type u → Type u'} {g : Type v → Type u}

section functor

variables [functor f] [functor g]
variables {α β γ : Type v}

def map (h : α → β) : compose f g α → compose f g β
  | ⟨ x ⟩ := ⟨ fmap h <$> x ⟩

local infix ` <$> ` := map

lemma id_map : ∀ (x : compose f g α), map id x = x
  | ⟨ x ⟩ :=
by { unfold map, rw [functor.id_map',functor.id_map], }

lemma map_comp (g_1 : α → β) (h : β → γ) : ∀ (x : compose f g α),
           map (h ∘ g_1) x = map h (map g_1 x)
  | ⟨ x ⟩ :=
by { unfold map, rw [functor.map_comp' g_1 h,functor.map_comp], }

end functor
end compose

instance functor_compose {f : Type u → Type u'} {g : Type v → Type u}
  [functor f] [functor g]
: functor (compose f g) :=
{ map := @compose.map f g _ _
, id_map := @compose.id_map f g _ _
, map_comp := @compose.map_comp f g _ _ }

lemma compose.fmap_mk {α β : Type u'}
  {f : Type u → Type v} {g : Type u' → Type u}
  [functor f] [functor g]
  (h : α → β) (x : f (g α))
: h <$> compose.mk x = compose.mk (fmap h <$> x) := rfl
