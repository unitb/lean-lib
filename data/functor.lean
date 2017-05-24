
universe variables u v w u' v' w'

class functor_pair (f : Type u → Type v) (g : Type u' → Type v') :=
 (f_functor : functor f)
 (g_functor : functor g)
 (map : ∀ {α β}, (α → β) → f α → g β)
 (map_fmap_comm : ∀ {α β β' γ}
            (h : β → γ)    (hp : α → β)
            (hp' : β' → γ) (h' : α → β')
            (x : f α),
    h ∘ hp = hp' ∘ h' →
    has_map.map h (map hp x) = map hp' (has_map.map h' x))

section thms

variables {F : Type u → Type v}
variables {α β γ : Type u}
variables [functor F]

lemma functor.id_map' : has_map.map id = (id : F α → F α) :=
by { apply funext, apply functor.id_map }

lemma functor.map_comp' (f : α → β) (g : β → γ)
: has_map.map (g ∘ f) = (has_map.map g ∘ has_map.map f : F α → F γ) :=
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

instance identity_functor : functor identity :=
{ map := @identity.map
, id_map := @identity.id_map
, map_comp := @identity.map_comp }

instance : functor_pair identity identity :=
{ f_functor := identity_functor
, g_functor := identity_functor
, map := @identity.map
, map_fmap_comm :=
  begin
    intros α β β' γ,
    intros h hp hp' h' x,
    intros H, unfold has_map.map,
    rw [-identity.map_comp,-identity.map_comp,H],
  end }

lemma identity.fmap_mk {α β : Type v}  (f : α → β) (x : α)
: f <$> identity.mk x = identity.mk (f x) := rfl

/- compose functor instance -/

structure compose (f : Type u → Type u') (g : Type v → Type u) (α : Type v) : Type u' :=
  (run_compose : f $ g α)

namespace compose

section functor

variables {f : Type u → Type u'} {g : Type v → Type u}

variables [functor f] [functor g]
variables {α β γ : Type v}

def map (h : α → β) : compose f g α → compose f g β
  | ⟨ x ⟩ := ⟨ has_map.map h <$> x ⟩

local infix ` <$> ` := map

lemma id_map : ∀ (x : compose f g α), map id x = x
  | ⟨ x ⟩ :=
by { unfold map, rw [functor.id_map',functor.id_map], }

lemma map_comp (g_1 : α → β) (h : β → γ) : ∀ (x : compose f g α),
           map (h ∘ g_1) x = map h (map g_1 x)
  | ⟨ x ⟩ :=
by { unfold map, rw [functor.map_comp' g_1 h,functor.map_comp], }

end functor
section functor_pair

variables {f  : Type v  → Type w}  {g :  Type u  → Type v}
variables {f' : Type v' → Type w'} {g' : Type u' → Type v'}

variables [functor_pair f f'] [functor_pair g g']
variables {α : Type u} {β : Type u'}

def map_pair (h : α → β) : compose f g α → compose f' g' β
  | ⟨ x ⟩ := ⟨ functor_pair.map f' (functor_pair.map g' h) x ⟩

end functor_pair
end compose

instance functor_compose {f : Type u → Type u'} {g : Type v → Type u}
  [functor f] [functor g]
: functor (compose f g) :=
{ map := @compose.map f g _ _
, id_map := @compose.id_map f g _ _
, map_comp := @compose.map_comp f g _ _ }

instance compose_functor_pair
  {f :  Type v  → Type w}  {g  : Type u  → Type v}
  {f' : Type v' → Type w'} {g' : Type u' → Type v'}
  [functor_pair f f'] [functor_pair g g']
: functor_pair (compose f g) (compose f' g') :=
{ f_functor := @functor_compose f g
       (functor_pair.f_functor f f')
       (functor_pair.f_functor g g')
, g_functor := @functor_compose f' g'
       (functor_pair.g_functor f f')
       (functor_pair.g_functor g g')
, map := @compose.map_pair f g _ _ _ _
, map_fmap_comm :=
  begin
    intros α β β' γ,
    intros h hp hp' h' x H,
    unfold has_map.map,
    cases x with x,
    unfold compose.map_pair compose.map,
    apply congr_arg,
    rw [functor_pair.map_fmap_comm],
    apply funext, intro i, unfold comp has_map.map,
    rw [functor_pair.map_fmap_comm],
    apply H,
  end }

lemma compose.fmap_mk {α β : Type u'}
  {f : Type u → Type v} {g : Type u' → Type u}
  [functor f] [functor g]
  (h : α → β) (x : f (g α))
: h <$> compose.mk x = compose.mk (has_map.map h <$> x) := rfl
