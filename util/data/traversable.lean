
import util.control.applicative
import util.control.monad
import util.data.functor
import util.data.ulift_t

open function

universe variables w u v w' u' v'

structure applicative_morphism
    {f : Type u → Type v} [applicative f]
    {g : Type u → Type w} [applicative g]
    (F : ∀ {α : Type u}, f α → g α) :=
  (preserves_pure : ∀ {α : Type u} (x : α), F (pure x) = pure x)
  (preserves_seq : ∀ {α β : Type u} (x : f (α → β)) (y : f α), F (x <*> y) = F x <*> F y)

class has_traverse (t : Type u → Type v) :=
(traverse' : Π {m : Type (max u v) → Type w} [applicative m]
   {α β : Type u},
   (α → m (ulift β)) → t α → m (ulift.{u} (t β)))

open ulift (up down up_down) has_map

export has_traverse (traverse')

section functions

variables {t : Type u → Type u}
variables {m : Type u → Type v} [applicative m]
variables {f : Type u → Type u} [applicative f]
variables {α β : Type u}

def traverse [has_traverse.{v} t]
  (f : α → m β)
: t α → m (t β) :=
map down ∘ traverse'.{v} (λ x : α, up <$> (f x))

def sequence [has_traverse.{u u u} t]
: t (f α) → f (t α) :=
traverse id

end functions

instance : has_map ulift :=
{ map := λ α β f, up ∘ f ∘ down }

class traversable (t : Type u → Type v)
extends has_traverse.{max u v} t, functor t
: Type (max v u+1) :=
(id_traverse : ∀ {α : Type u} (x : t α), traverse' (identity.mk ∘ up) x = ⟨ up x ⟩ )
(traverse_comp : ∀ {G H : Type (max u v) → Type (max u v)}
               [applicative G] [applicative H]
               {α β γ : Type u}
               (g : α → G (ulift.{v} β)) (h : β → H (ulift.{v} γ)) (x : t α),
   traverse' (compose.mk ∘ has_map.map (h ∘ down) ∘ g) x =
   ⟨ (traverse' h ∘ down) <$> traverse' g x ⟩)
(map_traverse : ∀ {G : Type (max u v) → Type (max u v)}
               [applicative G]
               {α β γ : Type u}
               (g : α → G (ulift.{v} β)) (h : β → γ)
               (x : t α),
               has_map.map (has_map.map h) <$> traverse' g x =
               traverse' (has_map.map (has_map.map h) ∘ g) x)
(morphism : ∀ {G H : Type (max u v) → Type (max u v)}
              [applicative G] [applicative H]
              {eta : ∀ {α}, G α → H α},
              applicative_morphism @eta →
              ∀ {α β : Type u} (f : α → G (ulift β)) (x : t α),
              eta (traverse' f x) = traverse' (eta ∘ f) x)


lemma down_map {α β : Type u}
  (f : α → β)
: down.{v} ∘ map f = f ∘ down.{v} :=
by { apply funext, intro, cases x, refl }

lemma map_identity_mk {α β : Type u}
  (f : α → β)
: map f ∘ @identity.mk α = @identity.mk β ∘ f :=
rfl

section traversable

variable {t : Type u → Type u}
variable [traversable t]
variables {G H : Type u → Type u}
variables [applicative G] [applicative H]
variables {α β γ : Type u}
variables g : α → G β
variables h : β → H γ
variables f : β → γ

lemma id_traverse {x : t α}
: traverse identity.mk x = ⟨ x ⟩ :=
by simp [traverse,function.comp,map,identity.map,traversable.id_traverse x]

lemma functor.map_comp_rev {f : Type u → Type v} [functor f]
  (F : α → β) (G : β → γ) (x : f α)
: G <$> F <$> x = (G ∘ F) <$> x :=
by rw @functor.map_comp f _ _ _ _ F G x

lemma traverse_comp {x : t α}
: traverse (compose.mk ∘ map h ∘ g) x = ⟨ traverse h <$> traverse g x ⟩ :=
begin
  have H := traversable.traverse_comp (map up.{u u} ∘ g) (map up.{u u} ∘ h) x,
  simp [function.comp,functor.map_comp_rev] at *,
  simp [traverse],
  simp [function.comp,map,compose.map,functor.map_comp_rev,H],
end

lemma map_traverse {x : t α}
: map f <$> traverse g x = traverse (map f ∘ g) x :=
begin
  unfold traverse function.comp,
  simp [functor.map_comp_rev],
  have H := @traversable.map_traverse t _ G _ α β γ (map up ∘ g) f x,
  rw [← down_map,functor.map_comp],
  simp [H],
  tactic.congr,
  apply  funext, intro,
  simp [function.comp, functor.map_comp_rev,map],
end

lemma traverse_eq_map_ident {x : t β}
: traverse (identity.mk ∘ f) x = ⟨ f <$> x ⟩ :=
calc
      traverse (identity.mk ∘ f) x
    = traverse (map f ∘ identity.mk) x : by simp [map_identity_mk]
... = map f <$> traverse identity.mk x : by rw [← map_traverse]
... = map f <$> identity.mk x          : by simp [id_traverse]
... = ⟨ f <$> x ⟩                      : by refl

variable {eta : Π {α}, G α → H α}
variable (morph : applicative_morphism @eta)

include morph

lemma eta_map (x : G α) (f : α → β)
: map f (eta x) = eta (map f x) :=
begin
  symmetry,
  rw [← applicative.pure_seq_eq_map],
  rw [morph.preserves_seq,morph.preserves_pure,applicative.pure_seq_eq_map]
end

lemma traverse_morphism (x : t α) (h : α → G β)
: eta (traverse h x) = traverse (eta ∘ h) x :=
calc
       eta (traverse h x)
     = eta (down <$> traverse'.{u u} (λ (x : α), up <$> h x) x) : rfl
 ... = down <$> eta (traverse'.{u u u} (map up ∘ h) x) : by simp [eta_map morph]
 ... = down <$> traverse' (eta ∘ (map up ∘ h)) x     : by simp [traversable.morphism.{u u} morph]
 ... = down <$> traverse' (map up ∘ eta ∘ h) x       : by simp [function.comp,eta_map morph]
 ... = traverse (eta ∘ h) x                          : rfl

end traversable

namespace identity

open function

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

def traverse (g : α → f (ulift.{u} β)) : identity α → f (ulift.{u} (identity β))
 | ⟨ x ⟩ := (λ x : ulift.{u} β, up ⟨ down x ⟩) <$> g x

lemma traverse_mk (g : α → f (ulift.{u} β)) (x : α)
: traverse g ⟨ x ⟩ = (up ∘ mk ∘ down) <$> (g x) :=
rfl

lemma traverse_mk' (g : α → f (ulift.{u} β))
: traverse g ∘ mk = has_map.map (up ∘ mk ∘ down) ∘ g :=
rfl

lemma id_traverse (x : identity α)
: traverse (identity.mk ∘ up) x = identity.mk (up.{u} x) :=
by { cases x, unfold traverse, refl }

lemma traverse_comp (g : α → f (ulift.{u} β)) (h : β → f' (ulift.{u} γ)) : ∀ (x : identity α),
        traverse (compose.mk ∘ has_map.map (h ∘ down) ∘ g) x =
        compose.mk ((traverse h ∘ down) <$> traverse g x)
  | ⟨ x ⟩ :=
begin
  unfold traverse comp,
  rw [compose.fmap_mk],
  apply congr_arg,
  rw [← functor.map_comp,← functor.map_comp],
  refl,
end

lemma map_traverse
   (g : α → f' (ulift.{u} β)) (f : β → γ)
   (x : identity α)
: has_map.map (map f) <$> traverse g x = traverse (has_map.map (has_map.map f) ∘ g) x :=
sorry

variable {eta : ∀ {α}, f α → f' α}
variable morph : applicative_morphism @eta
include morph

lemma morphism {α β : Type u}
  (F : α → f (ulift.{u} β)) (x : identity α)
: eta (traverse F x) = traverse (eta ∘ F) x :=
sorry

end identity

instance : traversable identity :=
{ to_functor := (identity_functor : functor identity)
, traverse' := @identity.traverse
, id_traverse := λ α x, @identity.id_traverse α x
, traverse_comp := @identity.traverse_comp
, map_traverse := @identity.map_traverse
, morphism := @identity.morphism }

namespace option

open function

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

def traverse (g : α → f (ulift.{u} β)) : option α → f (ulift.{u} (option β))
 | none := pure (up none)
 | (some x) := (map some) <$> g x

lemma traverse_mk (g : α → f (ulift.{u} β)) (x : α)
: traverse g (some x) = map some <$> (g x) :=
rfl

lemma traverse_mk' (g : α → f (ulift.{u} β))
: traverse g ∘ some = has_map.map (map some) ∘ g :=
rfl

lemma id_traverse (x : option α)
: traverse (identity.mk ∘ up) x = ⟨ up x ⟩ :=
by { cases x ; unfold traverse ; refl }

lemma traverse_comp (g : α → f (ulift.{u} β)) (h : β → f' (ulift.{u} γ))
: ∀ (x : option α),
        traverse (compose.mk ∘ has_map.map (h ∘ down) ∘ g) x =
        compose.mk ((traverse h ∘ down) <$> traverse g x)
  | none :=
begin
  unfold traverse, rw applicative.map_pure,
  refl,
end
  | (some x) :=
begin
  unfold traverse comp,
  rw [compose.fmap_mk],
  apply congr_arg,
  rw [← functor.map_comp,← functor.map_comp],
  refl
end

lemma map_traverse (g : α -> f' (ulift.{u} β)) (f : β → γ)
  (x : option α)
: map (map f) <$> traverse g x = traverse (map (map f) ∘ g) x :=
by { cases x ; simp [traverse,comp,functor.map_comp_rev,applicative.map_pure] ; refl }

variable {eta : Π {α : Type u}, f α → f' α}
variable morph : applicative_morphism @eta
include morph

lemma morphism {α β : Type u} (g : α → f (ulift.{u} β)) (x : option α)
: eta (traverse g x) = traverse (eta ∘ g) x :=
sorry

end option

instance : traversable option :=
{ to_functor := _
, traverse' := @option.traverse
, id_traverse := @option.id_traverse
, traverse_comp := @option.traverse_comp
, map_traverse := @option.map_traverse
, morphism := @option.morphism }

namespace list

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

open applicative

def traverse (g : α → f (ulift.{u} β)) : list α → f (ulift.{u} (list β))
 | [] := pure $ up []
 | (x :: xs) := lift₂ cons <$> g x <*> traverse xs

lemma traverse_cons
  (g : α → f (ulift.{u} β))
  (x : f' (ulift.{u} α))
  (xs : f' (ulift.{u} (list α)))
: has_map.map (traverse g) <$> (lift₂ cons <$> x <*> xs) =
  lift₂ (lift₂ (lift₂ cons)) <$> (has_map.map g <$> x) <*> (has_map.map (traverse g) <$> xs) :=
begin
  rw [applicative.map_seq_assoc,← functor.map_comp],
  have H : (comp (has_map.map (traverse g)) ∘ lift₂ cons) =
           (lift₂ (λ x xs, lift₂ cons <$> g x <*> traverse g xs) : ulift _ → ulift _ → ulift _),
  { apply funext, intro x,
    apply funext, intro xs,
    refl },
  rw [H,functor.map_comp_rev,applicative.seq_map_comm,← functor.map_comp],
  refl
end

lemma id_traverse (xs : list α)
: traverse (identity.mk ∘ up) xs = ⟨ up xs ⟩ :=
begin
  induction xs with x xs IH ; unfold traverse,
  { refl },
  { simp [IH,identity.fmap_mk,identity.seq_mk,lift₂], refl },
end

lemma traverse_comp (g : α → f (ulift.{u} β)) (h : β → f' (ulift.{u} γ))
: ∀ (x : list α),
        traverse (compose.mk ∘ has_map.map (h ∘ down) ∘ g) x =
        compose.mk ((traverse h ∘ down) <$> traverse g x)
  | [] :=
begin
  unfold traverse, rw applicative.map_pure,
  simp [function.comp,traverse,up_down],
  refl
end
  | (x :: xs) :=
begin
  unfold traverse comp,
  rw [compose.fmap_mk,traverse_comp,compose.seq_mk],
  apply congr_arg,
  rw [functor.map_comp_rev],
  admit
end

lemma map_traverse {α β γ : Type u} (g : α → f' (ulift.{u} β)) (f : β → γ)
  (x : list α)
: has_map.map (map f) <$> traverse g x = traverse (has_map.map (has_map.map f) ∘ g) x :=
begin
  induction x with x xs ih,
  { simp [traverse,map_pure,comp,has_map.map] },
  { simp [traverse], rw ← ih, admit }
end

variable {eta : Π {α : Type u}, f α → f' α}
variable morph : applicative_morphism @eta
include morph

lemma morphism {α β : Type u} (g : α → f (ulift.{u} β)) (x : list α)
: eta (list.traverse g x) = list.traverse (eta ∘ g) x :=
sorry

end list

instance : traversable list :=
{ map := @list.map
, id_map := @list.map_id
, map_comp := by { introv, simp }
, traverse' := @list.traverse
, id_traverse := @list.id_traverse
, traverse_comp := @list.traverse_comp
, map_traverse := @list.map_traverse
, morphism := @list.morphism }

class foldable (f : Type u → Type v) : Type (max (u+1) (u'+1) v) :=
(foldr : Π {α : Type u} {r : Type u'}, (α → r → r) → f α → r → r)

def foldr' {f : Type u → Type v} [i : foldable f] {r : Type u'} {α : Type u} (g : α → r → r)
: f α → r → r :=
@foldable.foldr f i _ _ g

def foldr {f : Type u → Type v} [i : foldable f] {r : Type u'} {α : Type u} (g : α → r → r)
: r → f α → r :=
flip (@foldable.foldr f i _ _ g)

def to_list {f : Type u → Type v} [i : foldable f] {α : Type u} : f α → list α :=
@foldr f i _ _ list.cons []

def to_set' {f : Type u → Type v} [i : foldable f] {α : Type u} {r : Type u'}
  [has_insert α r]
  [has_emptyc r]
: f α → r :=
@foldr f i _ _ insert ∅

def to_set {f : Type u → Type v} [i : foldable f] {α : Type u}
: f α → set α :=
@to_set' f i _ _ _ _

def fold_map {f : Type u → Type v} [i : foldable f] {m : Type u'} [monoid m] {α : Type u}
  (g : α → m)
: f α → m :=
@foldr f i _ _ (has_mul.mul ∘ g) 1

def fold_map_add {f : Type u → Type v} [i : foldable f] {m : Type u'} [add_monoid m] {α : Type u}
  (g : α → m)
: f α → m :=
@foldr f i _ _ (has_add.add ∘ g) 0
