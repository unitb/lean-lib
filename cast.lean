
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

lemma option_cast_cast : ∀ {α β : Type u} (P₀ : α = β) (P₁ : β = α) (x : option β), option.cast(option.cast x P₁) P₀ = x
 | α ._ rfl rfl (some x) := rfl
 | α ._ rfl rfl none := rfl

lemma option_cast'_eq_option_cast : ∀ {α β : Type u} (P : α = β) (x : option β),
  option.cast' x P = option.cast x P.symm
 | α ._ rfl (some x) := rfl
 | α ._ rfl none := rfl

lemma option_cast_cast' : ∀ {α β : Type u} (P₀ P₁ : α = β) (x : option β),
  option.cast (option.cast' x P₁) P₀ = x
 | α ._ rfl rfl (some x) := rfl
 | α ._ rfl rfl none := rfl

lemma option_cast'_cast : ∀ {α β : Type u} (P₀ P₁ : α = β) (x : option α),
  option.cast' (option.cast x P₁) P₀ = x
 | α ._ rfl rfl (some x) := rfl
 | α ._ rfl rfl none := rfl
