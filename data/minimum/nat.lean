
import util.data.set
import util.data.minimum.basic

namespace nat

namespace wf

variable (s : set ℕ)
variable (P : s ≠ ∅)

def gt (P : s ≠ ∅) (i j : ℕ) : Prop :=
(∀ k, k ∈ s → k > j) ∧ i > j

lemma gt_accessible'
: ∀ (x y z k : ℕ), z ∈ s → z ≤ k + x  → gt s P y x → acc (gt s P) y
| x y z 0 Hz V P :=
begin
  have h := P.left z Hz,
  exfalso,
  apply not_le_of_gt h,
  simp at V,
  apply V,
end
| x y z (succ k) Hz V P :=
begin
  apply acc.intro _ (λ y', gt_accessible' y y' z k Hz _),
  apply le_trans V,
  rw [succ_add,-add_succ],
  apply add_le_add_left,
  apply P.right,
end

lemma gt_accessible (x y : ℕ)
  (h : gt s P y x)
: acc (gt s P) y :=
begin
  have Hex : ∃ z, z ∈ s := set.exists_mem_of_ne_empty P,
  cases Hex with z hz,
  have hz_le_zxx : z ≤ z - x + x,
  { rw [nat.sub_add_cancel],
    apply le_of_lt,
    apply h.left _ hz, },
  apply gt_accessible' s P x y z (z - x) hz hz_le_zxx h
end

def gt_wf (P : s ≠ ∅) : well_founded (gt s P) :=
⟨ λ x, ⟨ _, gt_accessible s P x ⟩ ⟩

variable {s}

lemma gt_of_not_mem {i j : ℕ}
(h₀ : ∀ (x : ℕ), x ∈ s → j ≤ x)
(h₁ : j ∉ s)
(h₂ : i > j)
: gt s P i j :=
begin
  unfold wf.gt, split,
  { intros k h,
    apply lt_of_le_of_ne (h₀ _ h),
    intro, subst j,
    cases h₁ h, },
  { apply h₂ }
end

end wf

section

variables (s : set ℕ)
variables [decidable_pred (λ x, x ∈ s)]
variables (P : s ≠ ∅)

def minimum_aux
: Π i, (∀ j, j ∈ s → i ≤ j) → ℕ :=
well_founded.fix (wf.gt_wf s P) $ λ x f P',
  if h : x ∈ s
  then x
  else
    have h₀ : ∀ (j : ℕ), j ∈ s → succ x ≤ j,
      begin intros j h₁,
            apply succ_le_of_lt,
            apply lt_of_le_of_ne,
            { apply P' _ h₁ },
            { intro h₂, subst x, contradiction },
      end,
    f (succ x) ⟨h₀, lt_succ_self _⟩ h₀

variables [decidable (s = ∅)]

protected def minimum : ℕ :=
have h' : ∀ (j : ℕ), j ∈ s → 0 ≤ j,
   from take j _, zero_le j,
if h : s = ∅ then 0
              else minimum_aux s h 0 h'

include P

lemma minimum.induction_aux (i : ℕ)
  {p : ℕ → Prop}
  (h₀ : ∀ i, (∀ j, j ∈ s → i ≤ j) → i ∈ s → p i)
  (h₁ : ∀ j, j ∈ s → i ≤ j)
: p (nat.minimum_aux s P i h₁) :=
begin
  revert h₁,
  apply well_founded.induction (wf.gt_wf s P) i _,
  intros i IH h₁,
  unfold minimum_aux,
  rw well_founded.fix_eq,
  cases decidable.em (i ∈ s) with h₂ h₂,
  { rw dif_pos h₂,
    apply h₀ _ h₁ h₂, },
  { rw dif_neg h₂,
    apply IH,
    apply wf.gt_of_not_mem _ h₁ h₂,
    apply lt_succ_self }
end

lemma minimum.induction
  (p : ℕ → Prop)
  (h : ∀ i, (∀ j, j ∈ s → i ≤ j) → i ∈ s → p i)
: p (nat.minimum s) :=
begin
  unfold nat.minimum,
  rw dif_neg P,
  apply minimum.induction_aux _ _ _ h,
end

end

section

parameter (s : set ℕ)
parameter [decidable_pred (λ x, x ∈ s)]
parameter (P : s ≠ ∅)
local infix ` ≻ `:50 := wf.gt s P

parameter [decidable (s = ∅)]

protected lemma minimum_mem
  (hnemp : s ≠ ∅)
: nat.minimum s ∈ s :=
begin
  apply nat.minimum.induction s hnemp (λ i, i ∈ s),
  intros i h₀ h₁, apply h₁,
end

protected lemma minimum_le
  (x : ℕ)
  (hmem : x ∈ s)
: nat.minimum s ≤ x :=
begin
  apply nat.minimum.induction s (set.ne_empty_of_mem hmem) (λ i, i ≤ x),
  intros i h₀ h₁, apply h₀ _ hmem,
end

protected lemma le_minimum_of_forall_le (x : ℕ)
  (h₀ : s ≠ ∅)
  (h₁ : ∀ (y : ℕ), y ∈ s → x ≤ y)
: x ≤ nat.minimum s :=
begin
  revert h₁,
  apply nat.minimum.induction s h₀ (λ i, (∀ (y : ℕ), y ∈ s → x ≤ y) → x ≤ i),
  intros i h₀ h₁ h₂,
  apply h₂ _ h₁,
end

end

end nat

local attribute [instance] classical.prop_decidable

noncomputable instance : has_minimum ℕ :=
{ (_ : weak_order ℕ) with
  minimum := λ s, nat.minimum s
, minimum_le := λ s, nat.minimum_le s
, le_minimum_of_forall_le := λ s, nat.le_minimum_of_forall_le s
, minimum_mem := λ s, nat.minimum_mem s }
