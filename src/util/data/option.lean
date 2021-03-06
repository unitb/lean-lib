
universe variables u v

variables {α : Type u}
variables {β : Type u}

@[simp]
lemma none_or_else (x : option α)
: (none <|> x) = x :=
by { cases x ; refl }

@[simp]
lemma or_else_none (x : option α)
: (x <|> none) = x :=
by { cases x ; refl }

@[simp]
lemma some_or_else (x : α) (y : option α)
: (some x <|> y) = some x :=
by { refl }

@[simp]
lemma or_else_assoc (x y z : option α)
: ((x <|> y) <|> z) = (x <|> (y <|> z)) :=
by { cases x ; simp }

@[simp]
lemma or_else_eq_none_iff (x y : option α)
: (x <|> y) = none ↔ x = none ∧ y = none :=
begin
  split ; intros h,
  cases x with x,
  { simp at h, simp [h] },
  { simp at h, contradiction },
  { simp [h.left,h.right] }
end

@[simp]
lemma fmap_none (f : α → β)
: f <$> none = none := rfl

@[simp]
lemma fmap_some (f : α → β) (x : α)
: f <$> some x = some (f x) := rfl

@[simp]
lemma fmap_eq_none_iff (f : α → β) (x : option α)
: f <$> x = none ↔ x = none :=
by cases x ; simp

@[simp]
lemma coe_eq_some (x : α)
: ↑x = some x :=
rfl

lemma is_some_of_eq_some {α : Type u}
  (x : α) {y : option α}
  (h : some x = y)
: y.is_some :=
begin
  rw [← h,option.is_some],
  exact rfl
end

namespace option

def to_suml {α β} (x : β) : option α → α ⊕ β
  | none := sum.inr x
  | (some y) := sum.inl y

def to_sumr {α β} (x : α) : option β → α ⊕ β
  | none := sum.inl x
  | (some y) := sum.inr y

end option
