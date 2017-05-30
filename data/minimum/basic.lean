

import data.set

import util.data.finite
import util.data.fin
import util.data.order

open nat

universe variables u

class has_minimum (α : Type u) extends weak_order α :=
  (minimum : set α → α)
  (minimum_mem : ∀ s, s ≠ ∅ → minimum s ∈ s)
  (minimum_le : ∀ s x, x ∈ s → minimum s ≤ x)
  (le_minimum_of_forall_le : ∀ s x, s ≠ ∅ → (∀ y, y ∈ s → x ≤ y) → x ≤ minimum s)

class has_maximum (α : Type u) extends weak_order α :=
  (maximum : set α → α)
  (maximum_mem : ∀ s, s ≠ ∅ → maximum s ∈ s)
  (maximum_ge : ∀ s x, x ∈ s → x ≤ maximum s)
  (maximum_unique : ∀ s x, x ∈ s → (∀ y, y ∈ s → y ≤ x) → maximum s = x)

notation `↓` binders `, ` r:(scoped P, has_minimum.minimum P) := r

lemma min_eq_or_min_eq {α} [decidable_linear_order α] (x y : α)
: min x y = x ∨ min x y = y :=
begin
  apply or.imp min_eq_left min_eq_right,
  apply le_total
end

lemma exists_mem_of_ne_empty {α} {s : set α}
  (h : s ≠ ∅)
: ∃ x : α, x ∈ s :=
begin
  apply classical.by_contradiction,
  intro h',
  note h'' := forall_not_of_not_exists h',
  apply h,
  apply set.eq_empty_of_forall_not_mem,
  apply h''
end

section minimum

-- open has_minimum

parameters {α : Type u}
parameters [has_minimum α]
parameters {s : set α}
parameters {x : α}

lemma minimum_mem
: s ≠ ∅ → has_minimum.minimum s ∈ s :=
@has_minimum.minimum_mem _ _ _

lemma minimum_le
: x ∈ s → has_minimum.minimum s ≤ x :=
@has_minimum.minimum_le _ _ _ _

lemma le_minimum_of_forall_le
: s ≠ ∅ → (∀ y, y ∈ s → x ≤ y) → x ≤ has_minimum.minimum s :=
@has_minimum.le_minimum_of_forall_le _ _ _ _

lemma minimum_unique
  (h₀ : x ∈ s)
  (h₁ : ∀ y, y ∈ s → x ≤ y)
: has_minimum.minimum s = x :=
begin
  note h₂ := set.ne_empty_of_mem h₀,
  apply @le_antisymm α,
  { apply minimum_le h₀, },
  { apply le_minimum_of_forall_le h₂ h₁, },
end

lemma le_minimum_iff_forall_le
  (h : s ≠ ∅)
  (x : α)
: x ≤ (↓ x, x ∈ s) ↔ (∀ y, y ∈ s → x ≤ y) :=
begin
  split ; intro h₀,
  { intros y h₁, revert h₀,
    apply indirect_le_left_of_le x,
    apply has_minimum.minimum_le _ _ h₁, },
  { apply le_minimum_of_forall_le h h₀, },
end

end minimum

section has_minimum

parameters {α : Type u}
parameters [weak_order α]
parameters minimum : set α → α
local notation `↓` binders ` | ` r:(scoped P, has_minimum.minimum P) := r
parameters minimum_mem : ∀ (s : set α), s ≠ ∅ → minimum s ∈ s
parameters h : ∀ (s : set α) (x : α), x ≤ minimum s ↔ ∀ y, y ∈ s → x ≤ y
include minimum_mem h

section lemmas

variables s : set α
variables x : α
variables h₀ : x ∈ s

include h₀

private lemma minimum_le
: minimum s ≤ x :=
begin
  apply le_of_indirect_le_left,
  intros z h',
  rw h at h',
  apply h' _ h₀,
end

omit h₀

variables h₁ : s ≠ ∅
variables h₂ : ∀ (y : α), y ∈ s → x ≤ y
include h₁ h₂

private lemma le_minimum_of_forall_le
: x ≤ minimum s :=
begin
  rw h, apply h₂,
end

end lemmas

def has_minimum_of_le_minimum_iff : has_minimum α :=
{ (_ : weak_order α) with
  minimum := minimum
, minimum_mem := @minimum_mem
, minimum_le := @minimum_le
, le_minimum_of_forall_le := @le_minimum_of_forall_le }

end has_minimum
