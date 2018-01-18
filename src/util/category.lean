
universes u v w

variables {k : Sort u}

class has_comp (cat : k → k → Sort v) :=
  (comp : ∀ {α β γ}, cat β γ → cat α β → cat α γ)

infixl ` <<< `:2 := has_comp.comp _

class semigroupoid (cat : k → k → Sort v) extends has_comp cat :=
  (assoc : ∀ {α β γ φ} (x : cat γ φ) (y : cat β γ) (z : cat α β),
             ( x <<< (y <<< z) ) = ( (x <<< y) <<< z ) )

class category (cat : k → k → Sort v) extends semigroupoid cat :=
  (ident : ∀ {α}, cat α α)
  (left_ident : ∀ {α β} (x : cat α β), (ident <<< x) = x)
  (right_ident : ∀ {α β} (x : cat α β), (x <<< ident) = x)

export category (ident)

@[reducible]
def category.assoc := semigroupoid.assoc

attribute [simp] category.left_ident
attribute [simp] category.right_ident
attribute [simp] semigroupoid.assoc

instance arrow_cat : category (->) :=
  { ident := @id
  , comp := @function.comp
  , assoc := @function.comp.assoc
  , left_ident  := @function.comp.left_id
  , right_ident := @function.comp.right_id }

def kleisli (m : Sort u → Sort v) (a : Sort w) (b : Sort u) := a → m b

instance {m : Type u → Type v} [monad m] : category (kleisli m) :=
  { ident := λ α x, pure x
  , comp := λ α β γ (x : kleisli m β γ) (y : kleisli m α β), λ i, y i >>= x
  , assoc := by { intros, simp [has_comp.comp,monad.bind_assoc] }
  , left_ident  := by { intros, apply funext, intro, apply monad.bind_pure, }
  , right_ident := by { intros, apply funext, intro, apply monad.pure_bind, } }
