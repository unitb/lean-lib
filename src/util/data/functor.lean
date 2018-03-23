
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
    functor.map h (map hp x) = map hp' (functor.map h' x))

section thms

variables {F : Type u → Type v}
variables {α β γ : Type u}
variables [functor F] [is_lawful_functor F]

lemma functor.id_map' : functor.map id = (id : F α → F α) :=
by { apply funext, apply is_lawful_functor.id_map }

lemma functor.comp_map' (f : α → β) (g : β → γ)
: functor.map (g ∘ f) = (functor.map g ∘ functor.map f : F α → F γ) :=
by { apply funext, intro, apply is_lawful_functor.comp_map }

@[norm]
lemma functor.map_map (f : α → β) (g : β → γ) (x : F α) :
  g <$> f <$> x = (g ∘ f) <$> x :=
by rw ← comp_map

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

lemma comp_map (f : α → β) (g : β → γ)
: ∀ (x : identity α), map (g ∘ f) x = g <$> f <$> x
 | ⟨ x ⟩ := rfl

end identity

instance identity_functor : functor identity :=
{ map := @identity.map }
instance identity_lawful_functor : is_lawful_functor identity :=
{ id_map := @identity.id_map
, comp_map := @identity.comp_map }

instance : functor_pair identity identity :=
{ f_functor := identity_functor
, g_functor := identity_functor
, map := @identity.map
, map_fmap_comm :=
  begin
    intros α β β' γ,
    intros h hp hp' h' x,
    intros H,
    rw [← identity.comp_map,← identity.comp_map,H],
  end }

lemma identity.fmap_mk {α β : Type v}  (f : α → β) (x : α)
: f <$> identity.mk x = identity.mk (f x) := rfl

/- compose functor instance -/

structure compose (f : Type u → Type u') (g : Type v → Type u) (α : Type v) : Type u' :=
  (run : f $ g α)

namespace compose

section functor

variables {f : Type u → Type u'} {g : Type v → Type u}

variables [functor f] [functor g]
variables {α β γ : Type v}

def map (h : α → β) : compose f g α → compose f g β
  | ⟨ x ⟩ := ⟨ functor.map h <$> x ⟩

local infix ` <$> ` := map

variables [is_lawful_functor f] [is_lawful_functor g]
variables {α β γ}

lemma id_map : ∀ (x : compose f g α), map id x = x
  | ⟨ x ⟩ :=
by simp! [functor.id_map']

lemma comp_map (g_1 : α → β) (h : β → γ) : ∀ (x : compose f g α),
           map (h ∘ g_1) x = map h (map g_1 x)
  | ⟨ x ⟩ :=
by simp [map,functor.comp_map' g_1 h,is_lawful_functor.comp_map (functor.map g_1)]
          { single_pass := tt }

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
{ map := @compose.map f g _ _ }

instance lawful_functor_compose {f : Type u → Type u'} {g : Type v → Type u}
  [functor f] [functor g]
  [is_lawful_functor f] [is_lawful_functor g]
: is_lawful_functor (compose f g) :=
{ id_map := λ _, @compose.id_map f g _ _ _ _ _
, comp_map := λ _ _ _, @compose.comp_map f g _ _ _ _ _ _ _ }

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
    unfold functor.map,
    cases x with x,
    unfold compose.map_pair compose.map,
    apply congr_arg,
    rw [functor_pair.map_fmap_comm],
    apply funext, intro i, unfold function.comp functor.map,
    rw [functor_pair.map_fmap_comm],
    apply H,
  end }

@[norm]
lemma compose.fmap_mk {α β : Type u'}
  {f : Type u → Type v} {g : Type u' → Type u}
  [functor f] [functor g]
  (h : α → β) (x : f (g α))
: h <$> compose.mk x = compose.mk (functor.map h <$> x) := rfl
