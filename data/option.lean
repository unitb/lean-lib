
universe variables u v

variables {α : Type u}
variables {β : Type u}

@[simp]
lemma none_or_else (x : option α)
: (none <|> x) = x :=
by { cases x ; refl }

@[simp]
lemma some_or_else (x : α) (y : option α)
: (some x <|> y) = some x :=
by { refl }

@[simp]
lemma fmap_none (f : α → β)
: f <$> none = none := rfl

@[simp]
lemma fmap_some (f : α → β) (x : α)
: f <$> some x = some (f x) := rfl
