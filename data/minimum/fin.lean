
import util.data.minimum.basic

open nat

namespace fin

section

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
  { apply @classical.epsilon_spec _ s,
    apply exists_mem_of_ne_empty h₀ }
end

end

end fin

noncomputable instance {n} : has_minimum (fin $ succ n) :=
{ (_ : weak_order (fin $ succ n)) with
  minimum := fin.minimum
, minimum_le := @fin.minimum_le _
, le_minimum_of_forall_le := @fin.le_minimum_of_forall_le _
, minimum_mem := @fin.minimum_mem _ }
