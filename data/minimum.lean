

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


-- lemma classical.epsilon_spec_entails {α} (p q : α → Prop)
--   (Hex : ∃ x, q x)
--   (Hall : ∀ x, q x → p x)
-- : p (@classical.epsilon α (nonempty_of_exists Hex) q) :=
-- begin
--   apply Hall,
--   apply classical.epsilon_spec,
-- end

namespace fin

section

open nat

parameter (n : ℕ)
@[reducible]
def t := fin n.succ
parameter {n}

def minimum_aux (s : set t)
  [decidable_pred (λ y : t, y ∈ s)]
: t → ∀ i : ℕ, i ≤ n.succ → t
  | x 0 P := x
  | x (nat.succ k) P := let y : t := ⟨k, P⟩ in
     if y ∈ s
     then minimum_aux (min x y) k (le_of_succ_le P)
     else minimum_aux x k $ le_of_succ_le P

protected noncomputable def minimum (s : set t) : t :=
have inst : decidable_pred (λ y : t, y ∈ s), from (λ _, classical.prop_decidable _),
@fin.minimum_aux _ inst (classical.epsilon s) n.succ
(by refl)  -- (by { unfold finite.count, apply lt_succ_self })

lemma minimum_mem_aux (s : set t) (y : t)
   [decidable_pred (λ x : t, x ∈ s)]
  (i : ℕ)
  (h : y ∈ s)
  (P : i ≤ n.succ)
: minimum_aux s y i P ∈ s :=
begin
  revert y,
  induction i with i IH
  ; unfold minimum_aux
  ; intros y h,
  { apply h },
  simp,
  cases decidable.em (({val := i, is_lt := P} : t n) ∈ s) with h' h',
  { rw if_pos h',
    apply IH,
    cases min_eq_or_min_eq y ({val := i, is_lt := P}) with h₀ h₀
    ; rw h₀
    ; assumption  },
  { rw if_neg h',
    apply IH _ _ h, },
end

lemma minimum_mem (s : set t) (h : s ≠ ∅)
: fin.minimum s ∈ s :=
begin
  apply minimum_mem_aux,
  apply classical.epsilon_spec (exists_mem_of_ne_empty h),
end

lemma minimum_le_min_aux (s : set t) (x : t)
  [decidable_pred (λ x : t, x ∈ s)]
  (i : ℕ)
  (P : i ≤ n.succ)
: minimum_aux s x i P ≤ x :=
begin
  revert x,
  induction i with i IH
  ; intro x
  ; unfold minimum_aux,
  { refl },
  { simp,
    cases decidable.em (({val := i, is_lt := P} : t n) ∈ s) with h h,
    { rw if_pos h,
      transitivity,
      apply IH,
      apply min_le_left, },
    { rw if_neg h,
      apply IH } },
end

lemma minimum_le_aux (s : set t) (x y : t)
   [decidable_pred (λ x : t, x ∈ s)]
  (i : ℕ)
  (hy : y ∈ s)
  (hx : x ∈ s)
  (Hxy : x.val < i)
  (P : i ≤ n.succ)
: minimum_aux s y i P ≤ x :=
begin
  revert y,
  induction i with i IH ; intros y hy,
  { cases not_lt_zero _ Hxy, },
  { cases lt_or_eq_of_le (succ_le_of_lt Hxy) with h' h',
    { unfold fin.minimum_aux, simp,
      cases decidable.em (({val := i, is_lt := P} : t n) ∈ s) with h₇ h₇,
      { rw if_pos h₇,
        apply IH,
        apply lt_of_succ_lt_succ h' ,
        cases min_eq_or_min_eq y {val := i, is_lt := P} with h'' h''
        ; rw h''
        ; assumption },
      { rw if_neg h₇,
        apply IH _ _ _ hy,
        apply lt_of_succ_lt_succ h', } },
    { assert h'' : ({ val := i, is_lt := P} : t n) = x,
      { symmetry,
        injection h' with h',
        apply fin.eq_of_veq, apply h' },
      rw -h'' at hx,
      unfold minimum_aux, simp,
      rw if_pos hx,
      rw h'',
      transitivity,
      apply minimum_le_min_aux,
      apply min_le_right } },
end

protected lemma minimum_le {s : set t} {x : t}
  (h : x ∈ s)
: fin.minimum s ≤ x :=
begin
  unfold minimum,
  apply minimum_le_aux,
  { apply @classical.epsilon_spec _ s ⟨_,h⟩ },
  { apply h },
  { apply fin.is_lt },
end

lemma minimum_aux_min
  (s : set t) (x y : t)
  [decidable_pred (λ x : t, x ∈ s)]
  (i : ℕ)
  (P : i ≤ n.succ)
: minimum_aux s (min x y) i P = min (minimum_aux s x i P) y :=
begin
  revert x,
  induction i with i IH
  ; intro x
  ; unfold minimum_aux,
  { refl },
  { simp,
    cases decidable.em (({val := i, is_lt := P} : t n) ∈ s) with Hmem Hmem,
    { rw [if_pos Hmem,if_pos Hmem,min_assoc,min_comm y,-min_assoc,IH], },
    { rw [if_neg Hmem,if_neg Hmem,IH], }, }
end

lemma minimum_unique_aux (s : set t) (x y : t)
  [decidable_pred (λ x : t, x ∈ s)]
  (i : ℕ)
  (P : i ≤ n.succ)
  (h₀ : s ≠ ∅)
  (h₁ : ∀ y, y ∈ s → x ≤ y)
  (h₂ : x.val < i)
  (h₃ : y ∈ s)
: x ≤ minimum_aux s y i P :=
begin
  induction i with i IH
  ; unfold minimum_aux,
  { cases not_lt_zero _ h₂, },
  { simp,
    cases nat.eq_or_lt_of_le h₂ with Heq Hlt,
      -- case Heq : nat.succ (x.val) = nat.succ i
    { injection Heq with Heq', clear Heq,
      assert Hx_g : ({val := i, is_lt := P} : t n) = x,
      { symmetry,
        apply fin.eq_of_veq,
        apply Heq' },
      cases decidable.em (x ∈ s) with Hmem Hmem,
      { rw [Hx_g,if_pos Hmem],
        rw [minimum_aux_min],
        rw min_eq_right,
        apply h₁,
        apply minimum_mem_aux,
        apply h₃ },
      { rw [Hx_g,if_neg Hmem],
        apply h₁, apply minimum_mem_aux _ _ _ h₃, } },
      -- case Hlt : nat.succ (x.val) < nat.succ i
    { rw [minimum_aux_min],
      { assert Hx_lt_mini : x ≤ (minimum_aux s y i (minimum_aux._main._proof_2 i P)),
        { apply IH,
          apply lt_of_succ_lt_succ Hlt, },
        cases decidable.em (({val := i, is_lt := P} : t n) ∈ s) with Hmem Hmem,
        { rw if_pos Hmem,
          apply le_min Hx_lt_mini,
          { rw le_def,
            apply le_of_lt,
            apply lt_of_succ_lt_succ Hlt, }, },
        { rw if_neg Hmem, apply Hx_lt_mini } } } },
end

protected lemma le_minimum_of_forall_le (s : set t) (x : t)
  (h₀ : s ≠ ∅)
  (h₁ : ∀ y, y ∈ s → x ≤ y)
: x ≤ fin.minimum s :=
begin
  apply minimum_unique_aux,
  { apply h₀ },
  { apply h₁ },
  { apply fin.is_lt },
  { apply @classical.epsilon_spec _ s ⟨_,h₀⟩ }
end

end

end fin

noncomputable instance {n} : has_minimum (fin $ succ n) :=
{ (_ : weak_order (fin $ succ n)) with
  minimum := fin.minimum
, minimum_le := @fin.minimum_le _
, le_minimum_of_forall_le := @fin.le_minimum_of_forall_le _
, minimum_mem := @fin.minimum_mem _ }

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
  note h := P.left z Hz,
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
  note Hex : ∃ z, z ∈ s := exists_mem_of_ne_empty P,
  cases Hex with z hz,
  assert hz_le_zxx : z ≤ z - x + x,
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
