
import util.data.finite
import util.data.fin

open nat

lemma min_eq_or_min_eq {α} [decidable_linear_order α] (x y : α)
: min x y = x ∨ min x y = y :=
sorry

lemma exists_mem_of_ne_empty {α} (s : set α)
  (h : s ≠ ∅)
: ∃ x, x ∈ s :=
sorry


def decidable.minimum_aux {α} [pos_finite α] [decidable_linear_order α] (s : set α)
  [decidable_pred (λ y, y ∈ s)]
: α → ∀ i : ℕ, i ≤ finite.count α → α
  | x 0 P := x
  | x (succ n) P := let y := (pos_finite.to_nat α).g ⟨n, P⟩ in
     if y ∈ s
     then decidable.minimum_aux (min x y) n (le_of_succ_le P)
     else decidable.minimum_aux x n $ le_of_succ_le P

noncomputable def minimum {α} [pos_finite α] [decidable_linear_order α] (s : set α) : α :=
have inst : decidable_pred (λ y, y ∈ s), from (λ _, classical.prop_decidable _),
@decidable.minimum_aux _ _ _ _ inst (classical.epsilon s) (finite.count α)
(by { unfold finite.count, apply lt_succ_self })

lemma minimum_mem_aux {α} [pos_finite α] [decidable_linear_order α] (s : set α) (y : α)
   [decidable_pred (λ x, x ∈ s)]
  (i : ℕ)
  (h : y ∈ s)
  (P : i ≤ finite.count α)
: decidable.minimum_aux s y i P ∈ s :=
begin
  revert y,
  induction i with i IH
  ; unfold decidable.minimum_aux
  ; intros y h,
  { apply h },
  simp,
  cases decidable.em ((pos_finite.to_nat α).g {val := i, is_lt := P} ∈ s) with h' h',
  { rw if_pos h',
    apply IH,
    cases min_eq_or_min_eq y ((pos_finite.to_nat α).g {val := i, is_lt := P}) with h₀ h₀
    ; rw h₀
    ; assumption  },
  { rw if_neg h',
    apply IH _ _ h, },
end

lemma minimum_mem {α} [pos_finite α] [decidable_linear_order α] (s : set α) (h : s ≠ ∅)
: minimum s ∈ s :=
begin
  apply minimum_mem_aux,
  apply classical.epsilon_spec (exists_mem_of_ne_empty _ h),
end

lemma minimum_le_min_aux {α} [pos_finite α] [decidable_linear_order α] (s : set α) (x : α)
  [decidable_pred (λ x, x ∈ s)]
  (i : ℕ)
  (P : i ≤ finite.count α)
: decidable.minimum_aux s x i P ≤ x :=
begin
  revert x,
  induction i with i IH
  ; intro x
  ; unfold decidable.minimum_aux,
  { refl },
  { simp,
    cases decidable.em ((pos_finite.to_nat α).g {val := i, is_lt := P} ∈ s) with h h,
    { rw if_pos h,
      transitivity,
      apply IH,
      apply min_le_left, },
    { rw if_neg h,
      apply IH } },
end

lemma minimum_le_aux {α} [pos_finite α] [decidable_linear_order α] (s : set α) (x y : α)
   [decidable_pred (λ x, x ∈ s)]
  (i : ℕ)
  (hy : y ∈ s)
  (hx : x ∈ s)
  (Hxy : ((pos_finite.to_nat α).f x).val < i)
  (P : i ≤ finite.count α)
: decidable.minimum_aux s y i P ≤ x :=
begin
  revert y,
  induction i with i IH ; intros y hy,
  { cases not_lt_zero _ Hxy, },
  { cases lt_or_eq_of_le (succ_le_of_lt Hxy) with h' h',
    { unfold decidable.minimum_aux, simp,
      cases decidable.em ((pos_finite.to_nat α).g {val := i, is_lt := P} ∈ s) with h₇ h₇,
      { rw if_pos h₇,
        apply IH,
        apply lt_of_succ_lt_succ h' ,
        cases min_eq_or_min_eq y ((pos_finite.to_nat α).g {val := i, is_lt := P}) with h'' h''
        ; rw h''
        ; assumption },
      { rw if_neg h₇,
        apply IH _ _ _ hy,
        apply lt_of_succ_lt_succ h' , } },
    { assert h'' : (pos_finite.to_nat α).g {val := i, is_lt := P} = x,
      { symmetry, rw -bijection.inverse,
        injection h' with h',
        apply fin.eq_of_veq, apply h' },
      rw -h'' at hx,
      unfold decidable.minimum_aux, simp,
      rw if_pos hx,
      rw h'',
      transitivity,
      apply minimum_le_min_aux,
      apply min_le_right } },
end

lemma minimum_le {α} [pos_finite α] [decidable_linear_order α] (s : set α) (x : α) (h : x ∈ s)
: minimum s ≤ x :=
begin
  unfold minimum,
  apply minimum_le_aux,
  { apply @classical.epsilon_spec _ s ⟨_,h⟩ },
  { apply h },
  { apply fin.is_lt },
end

lemma minimum_aux_min {α}
  [pos_finite α] [decidable_linear_order α]
  (s : set α) (x y : α)
  [decidable_pred (λ x, x ∈ s)]
  (i : ℕ)
  (P : i ≤ finite.count α)
: decidable.minimum_aux s (min x y) i P = min (decidable.minimum_aux s x i P) y :=
begin
  revert x,
  induction i with i IH
  ; intro x
  ; unfold decidable.minimum_aux,
  { refl },
  { simp,
    cases decidable.em ((pos_finite.to_nat α).g {val := i, is_lt := P} ∈ s) with Hmem Hmem,
    { rw [if_pos Hmem,if_pos Hmem,min_assoc,min_comm y,-min_assoc,IH], },
    { rw [if_neg Hmem,if_neg Hmem,IH], }, }
end

lemma minimum_unique_aux {α} [pos_finite α] [decidable_linear_order α] (s : set α) (x y : α)
  [decidable_pred (λ x, x ∈ s)]
  (i : ℕ)
  (P : i ≤ finite.count α)
  (h₀ : x ∈ s)
  (h₁ : ∀ y, y ∈ s → x ≤ y)
  (h₂ : ((finite.to_nat α).f x).val < i)
  (h₃ : y ∈ s)
: decidable.minimum_aux s y i P = x :=
begin
  induction i with i IH
  ; unfold decidable.minimum_aux,
  { cases not_lt_zero _ h₂, },
  { simp,
    cases nat.eq_or_lt_of_le h₂ with Heq Hlt,
    { injection Heq with Heq', clear Heq,
      assert Hx_g : ((pos_finite.to_nat α).g {val := i, is_lt := P}) = x,
      { symmetry, rw -bijection.inverse,
        apply fin.eq_of_veq,
        apply Heq' },
      rw [Hx_g,if_pos h₀],
      rw [minimum_aux_min],
      apply min_eq_right,
      apply h₁,
      apply minimum_mem_aux,
      apply h₃,  },
    { rw [minimum_aux_min,IH],
      { cases decidable.em ((pos_finite.to_nat α).g {val := i, is_lt := P} ∈ s) with Hmem Hmem,
        { rw if_pos Hmem,
          apply min_eq_left,
          apply h₁ _ Hmem, },
        { rw if_neg Hmem, } },
      { apply lt_of_succ_lt_succ Hlt, },  } },
end

lemma minimum_unique {α} [pos_finite α] [decidable_linear_order α] (s : set α) (x : α)
  (h₀ : x ∈ s)
  (h₁ : ∀ y, y ∈ s → x ≤ y)
: minimum s = x :=
begin
  apply minimum_unique_aux,
  { apply h₀ },
  { apply h₁ },
  { apply fin.is_lt },
  { apply @classical.epsilon_spec _ s ⟨_,h₀⟩ }
end
