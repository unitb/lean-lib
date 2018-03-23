
import data.set.basic

import util.logic

namespace set

open function

universe variables u₀ u₁

lemma ne_empty_of_exists_mem {α} {s : set α}
  (h : ∃ x : α, x ∈ s)
: s ≠ ∅ :=
exists.elim h (@ne_empty_of_mem _ s)

variables {α : Type u₀} {β : Type u₀}
variables {s : set α}
variables {f : α → β}
variables {g : β → α}
variables (Hinj : injective f)

lemma mem_fmap_of_mem
  {x : α}
  (h : x ∈ s)
: f x ∈ f <$> s :=
begin
  unfold functor.map image,
  rw mem_set_of,
  exact ⟨x,h,rfl⟩
end

include Hinj

lemma mem_of_mem_fmap
  {x : α}
  (h : f x ∈ f <$> s)
: x ∈ s :=
begin
  unfold functor.map image at h,
  rw mem_set_of at h,
  cases h with y h₀, cases h₀ with h₀ h₁,
  rw ← Hinj h₁,
  apply h₀
end

lemma mem_fmap_iff_mem_of_inj
  {x : α}
: f x ∈ f <$> s ↔ x ∈ s :=
⟨ mem_of_mem_fmap Hinj, mem_fmap_of_mem ⟩

lemma mem_fmap_iff_mem_of_bij
  (Hinv : left_inverse f g)
  {x : β}
: x ∈ f <$> s ↔ g x ∈ s :=
begin
  have H : bijective f,
  { unfold bijective, split,
    { apply Hinj },
    { apply surjective_of_has_right_inverse,
      exact ⟨g,Hinv⟩ } },
  rw [← Hinv x,mem_fmap_iff_mem_of_inj Hinj,Hinv x]
end

omit Hinj

lemma fmap_eq_empty_iff_eq_empty
: f <$> s = ∅ ↔ s = ∅ :=
begin
  split
  ; intro h,
  { rw  eq_empty_iff_forall_not_mem,
    have h₁ := congr_fun h,
    intros x h₂,
    have h₃ := h₁ (f x),
    change (∅ : set β) (f x),
    rw ← iff_eq_eq at h₃,
    rw ← h₃, apply mem_fmap_of_mem h₂, },
  { rw h,
    rw eq_empty_iff_forall_not_mem,
    intros x h',
    unfold functor.map image at h',
    rw mem_set_of at h',
    cases h' with i h', cases h' with h₀ h₁,
    apply not_mem_empty _ h₀ },
end

end set
