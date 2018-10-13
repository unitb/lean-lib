
import data.stream
import util.logic
import util.data.nat
import util.data.stream

open nat function
open stream

def rounds : ℕ → ℕ → stream ℕ := curry $ coinduct rounds.f

lemma rounds_zero (m  : ℕ) :
rounds m 0 = 0 :: rounds (succ m) (succ m) :=
begin
  unfold rounds curry coinduct,
  apply stream.corec_eq
end

lemma rounds_succ (m n : ℕ) :
rounds m (succ n) = succ n :: rounds m n :=
by apply stream.corec_eq

section wf

open well_founded


end wf

def inf_interleave : stream ℕ :=
rounds 0 0

def is_suffix {α} (p q : stream α) : Prop := ∃ i, p = stream.drop i q

infix ` ⊑ `:70 := is_suffix

instance {α} : has_le (stream α) := { le := is_suffix }

section partial_order

variable {α : Type}
variables s s₀ s₁ s₂ : stream α

lemma stream.le_refl : s ⊑ s :=
begin
  unfold is_suffix,
  existsi 0,
  refl
end

lemma stream.le_trans : s₀ ⊑ s₁ → s₁ ⊑ s₂ → s₀ ⊑ s₂ :=
begin
  intros h₀ h₁,
  cases h₀ with i h₀,
  cases h₁ with j h₁,
  unfold is_suffix,
  existsi i+j,
  rw [← stream.drop_drop,← h₁,h₀],
end

end partial_order

theorem head_rounds : ∀ i j, stream.head (rounds i j) = j :=
begin
  intros i j,
  cases j with j
  ; simp [rounds_zero,rounds_succ,stream.head_cons]
end

theorem suffix_cons {α} (s : stream α) (x : α) : s ⊑ (x :: s) :=
begin
  unfold is_suffix,
  existsi 1, refl
end

lemma le_zero_of_eq_zero {n : ℕ} (h : n ≤ 0) : n = 0 :=
le_antisymm h (nat.zero_le _)

theorem suffix_self_of_le (i j k : ℕ) :
  j ≤ k →
  rounds i j ⊑ rounds i k :=
begin
  intro h,
  induction k with k,
  { have h' := le_zero_of_eq_zero h, subst j,
    apply stream.le_refl },
  cases decidable.em (j ≤ k) with h' h',
  { rw rounds_succ,
    apply stream.le_trans,
    { apply k_ih h' },
    { apply suffix_cons } },
  { have h' : j = succ k,
    { apply le_antisymm h,
      apply lt_of_not_le h' },
    rw h', apply stream.le_refl }
end

theorem rounds_succ_succ : ∀ i k, rounds (succ i) (succ i) ⊑ rounds i k :=
begin
  intros i k,
  unfold is_suffix,
  existsi (succ k),
  induction k with k,
  { simp [rounds_zero,stream.drop_succ,stream.tail_cons],refl },
  { rw k_ih, simp [rounds_succ,stream.drop_succ,stream.tail_cons] }
end

theorem is_prefix_add : ∀ (i j : ℕ), rounds (j+i) (j+i) ⊑ rounds j j
  | 0 j  := stream.le_refl _
  | (succ i) j :=
begin
  apply stream.le_trans,
  rw [add_succ],
  apply rounds_succ_succ (j+i) (j+i),
  apply is_prefix_add ,
end

theorem is_prefix_of_le (i j : ℕ) (h : j ≤ i) : rounds i i ⊑ rounds j j :=
begin
  have h' : i = j + (i - j),
  { rw [← nat.add_sub_assoc h, nat.add_sub_cancel_left] },
  rw h',
  apply is_prefix_add
end

section exist

universe variable u
variable {α : Type u}

variables P Q : α → Prop
variables Hq : ∀ x, P x → Q x

end exist

variable {α : Type}
variable i : ℕ
variable s : stream α

theorem rounds_suffix_rounds
  {s : stream ℕ}
  {i j : ℕ}
  (h₀ : j ≤ i)
  (h₁ : s ⊑ rounds i j)
: ∃ i' j', j' ≤ i' ∧ s = rounds i' j' :=
begin
  unfold is_suffix at h₁,
  cases h₁ with k h₁,
  subst s,
  revert i j,
  induction k with k ; intros i j Hij,
  { existsi i, existsi j,
    apply and.intro Hij,
    refl },
  { rw drop_succ,
    cases j with j,
    { rw [rounds_zero,tail_cons] ,
      have h' := @k_ih (succ i) (succ i) (nat.le_refl _),
      apply h',  },
    { have Hij' := nat.le_of_succ_le Hij,
      have h' := @k_ih i j Hij',
      rw [rounds_succ,tail_cons],
      apply h', } },
end

theorem inf_interleave_to_rounds_idx (s : stream ℕ) (h : s ⊑ inf_interleave)
: ∃ i j, j ≤ i ∧ s = rounds i j :=
begin
  apply rounds_suffix_rounds (le_refl _) h
end

theorem search_inf_interleave (s : stream ℕ) (x) (h : s ⊑ inf_interleave)
: ∃ s', s' ⊑ s ∧ head s' = x :=
begin
  cases (inf_interleave_to_rounds_idx s h) with i h₀,
  cases h₀ with j h₀,
  cases h₀ with h₁ h₀,
  existsi rounds (succ $ max i x) x,
  split,
  { rw h₀,
    apply stream.le_trans,
    { apply suffix_self_of_le,
      apply le_succ_of_le,
      apply le_max_right i x },
    apply stream.le_trans,
    { apply is_prefix_of_le _ (succ i),
      apply succ_le_succ,
      apply le_max_left },
    { apply rounds_succ_succ _ j } },
  { apply head_rounds }
end

theorem inf_repeat_inf_inter : ∀ x i, ∃ j, inf_interleave (i+j) = x :=
begin
  intros x i,
  have h' : drop i inf_interleave ⊑ inf_interleave,
  { unfold is_suffix, existsi i, refl },
  have h  := search_inf_interleave (drop i inf_interleave) x h',
  cases h with s' h,
  cases h with h₀ h₁,
  unfold is_suffix at h₀,
  cases h₀ with y h₀,
  existsi y,
  rw [drop_drop,add_comm] at h₀,
  change (nth (i + y) inf_interleave) = _,
  rw [← head_drop,← h₀,h₁]
end
