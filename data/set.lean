
import data.set

import util.logic

namespace set

open function

universe variables u₀ u₁

variables {α : Type u₀} {β : Type u₀}
variables {s : set α}
variables {f : α → β}
variables (Hinj : injective f)

include Hinj

lemma mem_of_mem_fmap
  {x : α}
  (h : f x ∈ f <$> s)
: x ∈ s :=
begin
  unfold has_map.map image at h,
  rw mem_set_of at h,
  cases h with y h₀, cases h₀ with h₀ h₁,
  rw -Hinj h₁,
  apply h₀
end

omit Hinj

lemma mem_fmap_of_mem
  {x : α}
  (h : x ∈ s)
: f x ∈ f <$> s :=
begin
  unfold has_map.map image,
  rw mem_set_of,
  exact ⟨x,h,rfl⟩
end

lemma fmap_eq_empty_iff_eq_empty
: f <$> s = ∅ ↔ s = ∅ :=
begin
  split
  ; intro h,
  { apply eq_empty_of_forall_not_mem,
    note h₁ := congr_fun h,
    intros x h₂,
    note h₃ := h₁ (f x),
    change (∅ : set β) (f x),
    rw -iff_eq_eq at h₃,
    rw - h₃, apply mem_fmap_of_mem h₂, },
  { rw h,
    apply eq_empty_of_forall_not_mem,
    intros x h',
    unfold has_map.map image at h',
    rw mem_set_of at h',
    cases h' with i h', cases h' with h₀ h₁,
    apply not_mem_empty _ h₀ },
end

end set
