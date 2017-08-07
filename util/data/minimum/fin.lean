
import util.data.fin
import util.data.minimum.nat
import util.data.set
import util.logic

open nat

namespace fin

section

parameter (n : ℕ)
@[reducible]
def t := fin n.succ
parameter {n}
variables (s : set t)
variables [decidable_pred (λ y : ℕ, y ∈ val <$> s)]
variables [decidable (val <$> s = ∅)]

lemma lt_of_mem_fin_set {k : ℕ}
  (h : k ∈ val <$> s)
: k < n.succ :=
begin
  unfold has_map.map set.image at h,
  rw [mem_set_of] at h,
  cases h with i h, cases h with h₀ h₁,
  rw ← h₁, apply i.is_lt
end

lemma nat_minimum_bounded
: nat.minimum (val <$> s) < n.succ :=
begin
  cases decidable.em (val <$> s = ∅) with h h,
  { unfold nat.minimum,
    rw dif_pos h, apply zero_lt_succ },
  { have h' := nat.minimum_mem (val <$> s) h,
    apply lt_of_mem_fin_set _ h', },
end

protected def minimum : t :=
let r := nat.minimum (fin.val <$> s) in
have hr : r < nat.succ n, from nat_minimum_bounded _,
⟨r,hr⟩

lemma minimum_mem
  (h : s ≠ ∅)
: fin.minimum s ∈ s :=
begin
  apply set.mem_of_mem_fmap fin.val_injective,
  apply nat.minimum_mem,
  simp [@set.fmap_eq_empty_iff_eq_empty _ _ s val,h],
end

protected lemma minimum_le {x : t}
  (h : x ∈ s)
: fin.minimum s ≤ x :=
begin
  simp [le_def],
  apply nat.minimum_le,
  apply set.mem_fmap_of_mem h,
end

protected lemma le_minimum_of_forall_le (x : t)
  (h₀ : s ≠ ∅)
  (h₁ : ∀ y, y ∈ s → x ≤ y)
: x ≤ fin.minimum s :=
begin
  simp [le_def],
  apply nat.le_minimum_of_forall_le,
  { simp [set.fmap_eq_empty_iff_eq_empty,h₀], },
  { intros y h,
    have hy := lt_of_mem_fin_set _ h,
    change x.val ≤ fin.val ⟨y,hy⟩,
    rw ← le_def,
    apply h₁,
    apply set.mem_of_mem_fmap val_injective, apply h, },
end

end

end fin

local attribute [instance] classical.prop_decidable

noncomputable instance {n} : has_minimum (fin $ succ n) :=
{ (_ : weak_order (fin $ succ n)) with
  minimum := λ s, fin.minimum s
, minimum_le := λ s x h, fin.minimum_le s h
, le_minimum_of_forall_le := λ s, fin.le_minimum_of_forall_le s
, minimum_mem := λ s, fin.minimum_mem _ }
