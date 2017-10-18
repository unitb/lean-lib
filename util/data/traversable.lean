/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Type class for traversing collections

This is a work-in-progress
-/

import util.control.applicative
import util.control.monad
import util.data.functor
import util.data.ulift_t

open function

universe variables w u v w' u' v'

section applicative_morphism

variables {f : Type u → Type v} [applicative f]
variables {g : Type u → Type w} [applicative g]
variables (F : ∀ {α : Type u}, f α → g α)

structure applicative_morphism : Prop :=
  (preserves_pure : ∀ {α : Type u} (x : α), F (pure x) = pure x)
  (preserves_seq : ∀ {α β : Type u} (x : f (α → β)) (y : f α), F (x <*> y) = F x <*> F y)

variables {F}
variables morph : applicative_morphism @F
include morph

lemma applicative_morphism.preserves_map {α β : Type u} (x : α → β)  (y : f α)
: F (x <$> y) = x <$> F y :=
by rw [← applicative.pure_seq_eq_map
      ,morph.preserves_seq
      ,morph.preserves_pure
      ,applicative.pure_seq_eq_map]

end applicative_morphism

class has_traverse (t : Type u → Type v) :=
(traverse' : Π {m : Type (max u v) → Type w} [applicative m]
   {α β : Type u},
   (α → m (ulift β)) → t α → m (ulift.{u} (t β)))

open ulift (up down up_down) has_map

export has_traverse (traverse')

section functions

variables {t : Type u → Type u}
variables {m : Type u → Type v} [applicative m]
variables {α β : Type u}

def traverse [has_traverse.{v} t]
  (f : α → m β)
: t α → m (t β) :=
map down ∘ traverse'.{v} (λ x : α, up <$> (f x))

variables {f : Type u → Type u} [applicative f]

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
  apply congr_arg,
  apply congr_fun,
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

lemma traverse_morphism (x : t α) (h : α → G β)
: eta (traverse h x) = traverse (eta ∘ h) x :=
calc
       eta (traverse h x)
     = eta (down <$> traverse'.{u u} (λ (x : α), up <$> h x) x) : rfl
 ... = down <$> eta (traverse'.{u u u} (map up ∘ h) x) : by simp [morph.preserves_map]
 ... = down <$> traverse' (eta ∘ (map up ∘ h)) x     : by simp [traversable.morphism.{u u} morph]
 ... = down <$> traverse' (map up ∘ eta ∘ h) x       : by simp [comp,morph.preserves_map]
 ... = traverse (eta ∘ h) x                          : rfl

end traversable

section identity

open function has_map

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

def identity.traverse (g : α → f (ulift.{u} β)) : identity α → f (ulift.{u} (identity β))
 | ⟨ x ⟩ := (λ x : ulift.{u} β, up ⟨ down x ⟩) <$> g x

instance : has_traverse.{v} identity :=
⟨ @identity.traverse ⟩

lemma identity.traverse_mk (g : α → f (ulift.{u} β)) (x : α)
: identity.traverse g ⟨ x ⟩ = (up ∘ identity.mk ∘ down) <$> (g x) :=
rfl

lemma identity.traverse_mk' (g : α → f (ulift.{u} β))
: identity.traverse g ∘ identity.mk = map (up ∘ identity.mk ∘ down) ∘ g :=
rfl

lemma identity.id_traverse (x : identity α)
: identity.traverse (identity.mk ∘ up) x = identity.mk (up.{u} x) :=
by { cases x, unfold identity.traverse, refl }

lemma identity.traverse_comp (g : α → f (ulift.{u} β)) (h : β → f' (ulift.{u} γ))
: ∀ (x : identity α),
        identity.traverse (compose.mk ∘ map (h ∘ down) ∘ g) x =
        compose.mk ((identity.traverse h ∘ down) <$> identity.traverse g x)
  | ⟨ x ⟩ :=
begin
  unfold identity.traverse comp,
  rw [compose.fmap_mk],
  apply congr_arg,
  rw [← functor.map_comp,← functor.map_comp],
  refl,
end

lemma identity.map_traverse
   (g : α → f' (ulift.{u} β)) (f : β → γ)
   (x : identity α)
: map (map f) <$> identity.traverse g x = identity.traverse (map (map f) ∘ g) x :=
begin
  cases x with x,
  simp [identity.traverse],
  repeat { rw [← functor.map_comp] },
  refl
end

variable {eta : ∀ {α}, f α → f' α}
variable morph : applicative_morphism @eta
include morph

lemma identity.morphism {α β : Type u}
  (F : α → f (ulift.{u} β)) (x : identity α)
: eta (identity.traverse F x) = identity.traverse (eta ∘ F) x :=
begin
  cases x with x,
  simp [identity.traverse,comp],
  rw [morph.preserves_map],
end

end identity

instance : traversable identity :=
{ to_functor := (identity_functor : functor identity)
, traverse' := @identity.traverse
, id_traverse := λ α x, @identity.id_traverse α x
, traverse_comp := @identity.traverse_comp
, map_traverse := @identity.map_traverse
, morphism := @identity.morphism }

section option

open function has_map

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

def option.traverse (g : α → f (ulift.{u} β)) : option α → f (ulift.{u} (option β))
 | none := pure (up none)
 | (some x) := map some <$> g x

lemma option.traverse_mk (g : α → f (ulift.{u} β)) (x : α)
: option.traverse g (some x) = map some <$> (g x) :=
rfl

lemma option.traverse_mk' (g : α → f (ulift.{u} β))
: option.traverse g ∘ some = map (map some) ∘ g :=
rfl

lemma option.id_traverse (x : option α)
: option.traverse (identity.mk ∘ up) x = ⟨ up x ⟩ :=
by { cases x ; unfold option.traverse ; refl }

lemma option.traverse_comp (g : α → f (ulift.{u} β)) (h : β → f' (ulift.{u} γ))
: ∀ (x : option α),
        option.traverse (compose.mk ∘ map (h ∘ down) ∘ g) x =
        compose.mk ((option.traverse h ∘ down) <$> option.traverse g x)
  | none :=
begin
  unfold option.traverse, rw applicative.map_pure,
  refl,
end
  | (some x) :=
begin
  unfold option.traverse comp,
  rw [compose.fmap_mk],
  apply congr_arg,
  rw [← functor.map_comp,← functor.map_comp],
  refl
end

lemma option.map_traverse (g : α -> f' (ulift.{u} β)) (f : β → γ)
  (x : option α)
: map (map f) <$> option.traverse g x = option.traverse (map (map f) ∘ g) x :=
by { cases x ; simp [option.traverse,comp,functor.map_comp_rev,applicative.map_pure] ; refl }

variable {eta : Π {α : Type u}, f α → f' α}
variable morph : applicative_morphism @eta
include morph

lemma option.morphism {α β : Type u} (g : α → f (ulift.{u} β)) (x : option α)
: eta (option.traverse g x) = option.traverse (eta ∘ g) x :=
begin
  cases x with x
  ; simp [option.traverse],
  { rw morph.preserves_pure },
  { rw morph.preserves_map }
end

end option

instance : traversable option :=
{ to_functor := _
, traverse' := @option.traverse
, id_traverse := @option.id_traverse
, traverse_comp := @option.traverse_comp
, map_traverse := @option.map_traverse
, morphism := @option.morphism }

section list

variables {f : Type u → Type v}
variables [applicative f]
variables {α β : Type u}

open applicative has_map
open list (cons)

def list.traverse (g : α → f (ulift.{u} β)) : list α → f (ulift.{u} (list β))
 | [] := pure $ up []
 | (x :: xs) := lift₂ cons <$> g x <*> list.traverse xs

end list

section list

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

open applicative has_map
open list (cons)

lemma list.traverse_cons
  (g : α → f (ulift.{u} β))
  (x : f' (ulift.{u} α))
  (xs : f' (ulift.{u} (list α)))
: map (list.traverse g) <$> (lift₂ cons <$> x <*> xs) =
  lift₂ (lift₂ (lift₂ cons)) <$> (map g <$> x) <*> (map (list.traverse g) <$> xs) :=
begin
  rw [applicative.map_seq_assoc,← functor.map_comp],
  have H : (comp (map (list.traverse g)) ∘ lift₂ cons) =
           (lift₂ (λ x xs, lift₂ cons <$> g x <*> list.traverse g xs)
             : ulift _ → ulift _ → ulift _),
  { apply funext, intro x,
    apply funext, intro xs,
    refl },
  rw [H,functor.map_comp_rev,applicative.seq_map_comm,← functor.map_comp],
  refl
end

lemma list.id_traverse (xs : list α)
: list.traverse (identity.mk ∘ up) xs = ⟨ up xs ⟩ :=
begin
  induction xs with x xs IH ; unfold list.traverse,
  { refl },
  { simp [IH,identity.fmap_mk,identity.seq_mk,lift₂], refl },
end

lemma list.traverse_comp (g : α → f (ulift.{u} β)) (h : β → f' (ulift.{u} γ))
: ∀ (x : list α),
        list.traverse (compose.mk ∘ map (h ∘ down) ∘ g) x =
        compose.mk ((list.traverse h ∘ down) <$> list.traverse g x)
  | [] :=
begin
  simp [list.traverse], rw applicative.map_pure,
  simp [function.comp,traverse,up_down],
  refl
end
  | (x :: xs) :=
begin
  unfold list.traverse comp,
  rw [compose.fmap_mk,list.traverse_comp,compose.seq_mk],
  apply congr_arg,
  simp [functor.map_comp_rev],
  repeat { rw [← applicative.pure_seq_eq_map] },
  simp [applicative.seq_assoc],
  repeat { rw [← applicative.pure_seq_eq_map] },
  simp [applicative.seq_assoc],
  repeat { rw [← applicative.pure_seq_eq_map] },
admit,
  -- apply congr_fun,
  -- apply congr_arg,
  -- apply congr,
  -- simp [applicative.seq_assoc],
  -- repeat { rw ← functor.map_comp },
  -- apply congr, refl
end

lemma list.map_traverse {α β γ : Type u} (g : α → f' (ulift.{u} β)) (f : β → γ)
  (x : list α)
: map (map f) <$> list.traverse g x = list.traverse (map (map f) ∘ g) x :=
begin
  induction x with x xs ih,
  { simp [list.traverse,map_pure,comp,map] },
  { simp [list.traverse], rw ← ih, admit }
end

variable {eta : Π {α : Type u}, f α → f' α}
variable morph : applicative_morphism @eta
include morph

lemma list.morphism {α β : Type u} (g : α → f (ulift.{u} β)) (x : list α)
: eta (list.traverse g x) = list.traverse (eta ∘ g) x :=
begin
  induction x with x xs
  ; simp [list.traverse],
  { simp [morph.preserves_pure] },
  { repeat { rw [← applicative.pure_seq_eq_map] },
  admit }
end

end list

instance : has_traverse.{v} list :=
{ traverse' := @list.traverse }

instance : traversable list :=
{ to_functor := _
, traverse' := @list.traverse
, id_traverse := @list.id_traverse
, traverse_comp := @list.traverse_comp
, map_traverse := @list.map_traverse
, morphism := @list.morphism }
