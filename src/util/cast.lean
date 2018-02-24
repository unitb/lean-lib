
universe variable u

def option.cast : ∀ {α β : Type u}, option α → (α = β) → option β
  | α ._ x rfl := x

@[reducible]
def option.cast' {α β : Type u} (x : option α) (P : β = α) : option β :=
option.cast x P.symm

lemma cast_some {α β} (x : α) (P : α = β) : (some x).cast P = some (cast P x) :=
begin
  cases P, refl
end

lemma cast_some' {α β} (x : β) (P : α = β) : (some x).cast' P = some (cast P.symm x) :=
begin
  cases P, refl
end

lemma cast_none : ∀ {α β} (P : α = β), none.cast P = none
 | α ._ rfl := rfl

lemma cast_none' : ∀ {α β} (P : α = β), none.cast' P = none
 | α ._ rfl := rfl

lemma cast_cast : ∀ {α β} (P₀ : α = β) (P₁ : β = α) (x : β), cast P₀ (cast P₁ x) = x
 | α ._ rfl rfl x := rfl

attribute [simp] cast_eq

@[simp]
lemma cast_cast' : ∀ {α β γ} (P₀ : γ = β) (P₁ : β = α) (x : γ), cast P₁ (cast P₀ x) = cast (by cc) x
 | α _ ._ rfl rfl x := rfl

lemma option_cast_cast {α : Type u}
: ∀ {β : Type u} (P₀ : α = β) (P₁ : β = α) (x : option β), option.cast(option.cast x P₁) P₀ = x
 | ._ rfl rfl (some x) := rfl
 | ._ rfl rfl none := rfl

lemma option_cast'_eq_option_cast {α : Type u}
: ∀ {β : Type u} (P : α = β) (x : option β), option.cast' x P = option.cast x P.symm
 | ._ rfl (some x) := rfl
 | ._ rfl none := rfl

lemma option_cast_cast' {α : Type u}
: ∀ {β : Type u} (P₀ P₁ : α = β) (x : option β), option.cast (option.cast' x P₁) P₀ = x
 | ._ rfl rfl (some x) := rfl
 | ._ rfl rfl none := rfl

lemma option_cast'_cast {α : Type u}
: ∀ {β : Type u} (P₀ P₁ : α = β) (x : option α), option.cast' (option.cast x P₁) P₀ = x
 | ._ rfl rfl (some x) := rfl
 | ._ rfl rfl none := rfl

open function

lemma option.cast_left_inverse {α β : Type u} (P : α = β)
: left_inverse (flip option.cast P) (flip option.cast' P) :=
option_cast_cast' P P

lemma option.cast_right_inverse {α β : Type u} (P : α = β)
: right_inverse (flip option.cast P) (flip option.cast' P) :=
option_cast'_cast P P

lemma option_cast_injective {α β : Type u} (P : α = β) : injective (flip option.cast P) :=
begin
  apply injective_of_left_inverse,
  apply option.cast_right_inverse,
end

lemma option_cast'_injective {α β : Type u} (P : α = β) : injective (flip option.cast' P) :=
begin
  apply injective_of_left_inverse,
  apply option.cast_right_inverse,
end
