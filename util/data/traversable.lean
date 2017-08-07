
import util.control.applicative
import util.data.functor

open function

structure {u v} cell (α : Type u) : Type (max u v) :=
  (get : α)

structure {u v} cell' (α : Type u) : Type (max v u) :=
  (get : α)

universe variables u v u'

class traversable (t : Type u → Type u) : Type (u+1) :=
(to_functor : functor t)
(traverse : Π {m : Type u → Type u} [applicative m] {α β : Type u},
   (α → m β) → t α → m (t β))
(id_traverse : Π {α : Type u}, traverse (identity.mk : α → identity α) = identity.mk)
(traverse_comp : Π (f f' : Type u → Type u)
               [applicative f] [applicative f']
               {α β γ : Type u}
               (g : α → f β) (h : β → f' γ) (x : t α),
        traverse (compose.mk ∘ has_map.map h ∘ g) x = compose.mk (traverse h <$> traverse g x))
(fmap_eq_traverse_id : Π {α β : Type u} (f : α → β),
        traverse (identity.mk ∘ f) = identity.mk ∘ has_map.map f)

namespace identity

open function

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

def traverse (g : α → f β) : identity α → f (identity β)
 | ⟨ x ⟩ := identity.mk <$> g x

lemma traverse_mk (g : α → f β) (x : α)
: traverse g (mk x) = mk <$> (g x) :=
rfl

lemma traverse_mk' (g : α → f β)
: traverse g ∘ mk = has_map.map mk ∘ g :=
rfl

lemma id_traverse : traverse (identity.mk : α → identity α) = identity.mk :=
by { apply funext, intro x, cases x, unfold traverse, refl }

lemma traverse_comp (g : α → f β) (h : β → f' γ) : ∀ (x : identity α),
        traverse (compose.mk ∘ has_map.map h ∘ g) x = compose.mk (traverse h <$> traverse g x)
  | ⟨ x ⟩ :=
begin
  unfold traverse comp,
  rw [compose.fmap_mk],
  apply congr_arg,
  rw [← functor.map_comp,← functor.map_comp,traverse_mk'],
end

lemma fmap_eq_traverse_id {α β : Type u} (f : α → β)
: traverse (identity.mk ∘ f) = identity.mk ∘ has_map.map f :=
by { apply funext, intro x, cases x, refl }

end identity

instance : traversable identity :=
{ to_functor := _
, traverse := @identity.traverse
, id_traverse := @identity.id_traverse
, traverse_comp := @identity.traverse_comp
, fmap_eq_traverse_id := @identity.fmap_eq_traverse_id }

namespace option

open function

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

def traverse (g : α → f β) : option α → f (option β)
 | none := pure none
 | (some x) := some <$> g x

lemma traverse_mk (g : α → f β) (x : α)
: traverse g (some x) = some <$> (g x) :=
rfl

lemma traverse_mk' (g : α → f β)
: traverse g ∘ some = has_map.map some ∘ g :=
rfl

lemma id_traverse : traverse (identity.mk : α → identity α) = identity.mk :=
by { apply funext, intro x, cases x ; unfold traverse ; refl }

lemma traverse_comp (g : α → f β) (h : β → f' γ) : ∀ (x : option α),
        traverse (compose.mk ∘ has_map.map h ∘ g) x = compose.mk (traverse h <$> traverse g x)
  | none :=
begin
  unfold traverse, rw applicative.map_pure,
  unfold traverse, unfold pure has_pure.pure compose.pure comp,
end
  | (some x) :=
begin
  unfold traverse comp,
  rw [compose.fmap_mk],
  apply congr_arg,
  rw [← functor.map_comp,← functor.map_comp,traverse_mk'],
end

lemma fmap_eq_traverse_id {α β : Type u} (f : α → β)
: traverse (identity.mk ∘ f) = identity.mk ∘ has_map.map f :=
by { apply funext, intro x, cases x ; refl }

end option

instance : traversable option :=
{ to_functor := _
, traverse := @option.traverse
, id_traverse := @option.id_traverse
, traverse_comp := @option.traverse_comp
, fmap_eq_traverse_id := @option.fmap_eq_traverse_id }

namespace list

variables {f f' : Type u → Type u}
variables [applicative f] [applicative f']
variables {α β γ : Type u}

def traverse (g : α → f β) : list α → f (list β)
 | [] := pure []
 | (x :: xs) := cons <$> g x <*> traverse xs

lemma traverse_cons (g : α → f β) (x : f' α) (xs : f' (list α))
: traverse g <$> (cons <$> x <*> xs) = (λ y ys, cons <$> y <*> ys) <$> (g <$> x) <*> (traverse g <$> xs) :=
begin
  rw [applicative.map_seq_assoc,← functor.map_comp],
  have H : function.comp (traverse g) ∘ cons = (λ x xs, cons <$> g x <*> traverse g xs),
  { apply funext, intro x,
    apply funext, intro xs,
    refl },
  rw [H,← functor.map_comp g,applicative.seq_map_comm,← functor.map_comp],
  refl
end

lemma id_traverse : traverse (identity.mk : α → identity α) = identity.mk :=
begin
  apply funext, intro x,
  induction x with x xs IH ; unfold traverse,
  { refl },
  { simp [IH,identity.fmap_mk,identity.seq_mk], },
end

lemma traverse_comp (g : α → f β) (h : β → f' γ) : ∀ (x : list α),
        traverse (compose.mk ∘ has_map.map h ∘ g) x = compose.mk (traverse h <$> traverse g x)
  | [] :=
begin
  unfold traverse, rw applicative.map_pure,
  unfold traverse, unfold pure has_pure.pure compose.pure comp,
end
  | (x :: xs) :=
begin
  unfold traverse comp,
  rw [compose.fmap_mk,traverse_comp,compose.seq_mk],
  apply congr_arg,
  rw [traverse_cons h,← functor.map_comp],
end

lemma fmap_eq_traverse_id {α β : Type u} (f : α → β)
: traverse (identity.mk ∘ f) = identity.mk ∘ has_map.map f :=
begin
  apply funext,
  intro x,
  induction x with x xs ih
  ; unfold traverse has_map.map,
  { refl },
  { rw ih, refl }
end

end list

instance : traversable list :=
{ to_functor := _
, traverse := @list.traverse
, id_traverse := @list.id_traverse
, traverse_comp := @list.traverse_comp
, fmap_eq_traverse_id := @list.fmap_eq_traverse_id }

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
