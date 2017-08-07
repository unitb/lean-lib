
import util.logic
import util.data.nat

open nat

universe variables u v

variables {α : Type u} {β : Type v}

lemma fin.veq_def {n} (x y : fin n)
: x = y ↔ x.val = y.val :=
begin
  split,
  apply fin.veq_of_eq,
  apply fin.eq_of_veq,
end

instance {n : ℕ} : inhabited (fin (succ n)) :=
inhabited.mk ⟨n,lt_succ_self _⟩

instance {n : ℕ} : decidable_linear_order (fin (succ n))  :=
  { le := has_le.le
  , lt := has_lt.lt
  , le_refl  := assume x, by simp [fin.le_def]
  , le_trans := assume x y z, by { simp [fin.le_def], apply le_trans }
  , le_antisymm := assume x y, by { simp [fin.le_def,fin.veq_def], apply le_antisymm }
  , le_total := assume x y, by { simp [fin.le_def], apply le_total }
  , le_iff_lt_or_eq := assume x y,
         by { rw [fin.le_def,fin.lt_def,fin.veq_def], apply le_iff_lt_or_eq }
  , lt_irrefl := assume x, by { simp [fin.lt_def], apply lt_irrefl }
  , decidable_eq := fin.decidable_eq _
  , decidable_le := fin.decidable_le
  , decidable_lt := fin.decidable_lt }

lemma fin.zero_def (n : ℕ)
: (0 : fin (succ n)).val = 0 :=
by refl

lemma fin.zero_def' (n : ℕ)
: (0 : fin (succ n)) = ⟨0, zero_lt_succ _ ⟩ :=
by { apply fin.eq_of_veq, rw fin.zero_def }

lemma fin.all_eq_zero (x : fin 1)
: x = 0 :=
by { cases x, cases val, refl, cases is_lt with i h, cases h, }

def fin.next {n : ℕ} : fin n → fin (succ n)
  | ⟨i,P⟩ := ⟨succ i, succ_lt_succ P⟩

def fin.pred' {n} : fin n → fin n
  | ⟨i,P⟩ := ⟨pred i,lt_of_le_of_lt (pred_le _) P⟩

def fin.succ' {n} : fin n → fin n
  | ⟨i,P⟩ := if P' : succ i < n then ⟨succ i,P'⟩
                                else ⟨i,P⟩

lemma fin.val_succ_le_nat_succ {n : ℕ} (x : fin n)
: x.succ'.val ≤ succ (x.val) :=
begin
  cases n with n
  ; cases x with x Pn
  ; unfold fin.succ' fin.val,
  { cases not_lt_zero _ Pn },
  cases decidable.em (succ x < succ n) with h h,
  { rw dif_pos h },
  { rw dif_neg h,
    apply le_succ },
end

lemma fin.pred_def {n : ℕ} (x : fin n)
: x.pred'.val = pred x.val :=
begin
  cases x with x Px,
  refl
end

lemma fin.succ_def  {n : ℕ} (x : fin n)
  (h : succ x.val < n)
: (x.succ').val = succ x.val :=
begin
  cases x with x Px,
  unfold fin.succ' fin.val,
  unfold fin.val at h,
  rw dif_pos h,
end

def fin.max {n} : fin (succ n) := ⟨n,lt_succ_self _⟩

lemma fin.max_def {n}
: (@fin.max n).val = n := rfl

lemma fin.pred_succ {n} (x : fin n)
  (h : succ x.val < n)
: x.succ'.pred' = x :=
begin
  apply fin.eq_of_veq,
  rw [fin.pred_def,fin.succ_def,pred_succ],
  apply h,
end

lemma fin.succ_pred {n} (x : fin (succ n))
  (h : 0 < x)
: x.pred'.succ' = x :=
begin
  apply fin.eq_of_veq,
  have h' : 0 < x.val,
  { rw [fin.lt_def,fin.zero_def] at h,
    apply h },
  rw [fin.succ_def,fin.pred_def,succ_pred_eq_of_pos h'],
  rw [fin.pred_def,succ_pred_eq_of_pos h'],
  apply x.is_lt,
end

lemma fin.succ_le_self {n} (x : fin (succ n))
  (h : x < fin.max)
: ¬ x.succ' ≤ x :=
begin
  rw [fin.le_def,fin.succ_def],
  apply not_succ_le_self,
  apply succ_lt_succ,
  rw [fin.lt_def,fin.max_def] at h,
  apply h
end

lemma fin.le_succ_self {n} (x : fin (succ n))
: x ≤ x.succ' :=
begin
  cases x with x Px,
  unfold fin.succ',
  cases decidable.em (succ x < succ n) with h h,
  { rw [dif_pos h,fin.le_def],
    apply le_succ },
  { rw [dif_neg h,fin.le_def], },
end

lemma fin.eq_zero_of_val_le_zero {n} (x : fin (succ n))
  (h : x.val ≤ 0)
: x = 0 :=
begin
  apply fin.eq_of_veq,
  rw fin.zero_def,
  apply le_antisymm h,
  apply zero_le
end

lemma fin.val_injective {n} : function.injective (@fin.val n)
 | ⟨x,_⟩ ⟨.(x),_⟩ rfl := rfl

def widen {n} : fin n → fin (nat.succ n)
| ⟨i,P⟩ := ⟨i,nat.le_succ_of_le P⟩

def restr {n α} (f : fin (nat.succ n) → α) (x : fin n) : α :=
f (widen x)

lemma widen_val {n : ℕ} (x : fin n)
: (widen x).val = x.val :=
by { cases x, refl }

lemma forall_fin_zero_iff_true (p : fin 0 → Prop)
: (∀ i, p i) ↔ true :=
begin
  split,
  { intros, trivial },
  { intros h' i, apply fin.elim0 i }
end

lemma forall_split_one {n : ℕ} (p : fin (nat.succ n) → Prop)
: (∀ i, p i) ↔ p fin.max ∧ (∀ i, restr p i) :=
begin
  split ; intro h,
  split,
  { apply h },
  { intro, apply h },
  { intro i, cases i with i hi,
    cases (lt_or_eq_of_le $ le_of_lt_succ hi) with h₀ h₁,
    { apply h.right ⟨i,h₀⟩ },
    { subst i, apply h.left } },
end

lemma exists_split_one {n : ℕ} (p : fin (nat.succ n) → Prop)
: (∃ i, p i) ↔ p fin.max ∨ (∃ i, restr p i) :=
begin
  rw [← not_iff_not_iff],
  simp [not_or_iff_not_and_not,not_exists_iff_forall_not,forall_split_one],
  refl
end

def fin.nest' {n m : ℕ} (H : m ≤ n) : fin m → fin n
  | ⟨i,P⟩ := ⟨i,lt_of_lt_of_le P H⟩

lemma fin.nest'_injective {n m : ℕ} (H : m ≤ n)
: function.injective (fin.nest' H) :=
begin
  intros i j,
  cases i with i Hi, cases j with j Hj,
  unfold fin.nest',
  intros H,
  apply fin.eq_of_veq, unfold fin.val,
  apply fin.veq_of_eq H,
end

def fin.nest {n m : ℕ} : fin m → fin (m + n)
  | ⟨i,P⟩ := ⟨i,lt_of_lt_of_le P (le_add_right m n)⟩

def fin.shift {n m : ℕ} : fin n → fin (m + n)
  | ⟨i,P⟩ := ⟨m+i,add_lt_add_left P _⟩

def fin.split {n m : ℕ} : fin (m + n) → fin m ⊕ fin n
  | ⟨k,P⟩ :=
if h : k < m
  then sum.inl ⟨k,h⟩
  else
    have h₀ : n = (m + n) - m, by rw nat.add_sub_cancel_left,
    have h₁ : k - m < n,
         begin rw h₀,
               apply nat.sub_lt_sub_right _ P,
               apply le_of_not_gt h
         end,
    sum.inr ⟨k-m,h₁⟩

def fin.unsplit {n m : ℕ} : fin m ⊕ fin n → fin (m + n)
  | (sum.inl n) := fin.nest n
  | (sum.inr n) := fin.shift n

lemma fin.split_nest {n m : ℕ} (k : fin m)
: fin.split (@fin.nest n m k) = sum.inl k :=
begin
  cases k with k Hk,
  unfold fin.shift fin.nest fin.split,
  rw dif_pos Hk
end

lemma fin.split_shift {n m : ℕ} (k : fin n)
: fin.split (@fin.shift n m k) = sum.inr k :=
begin
  cases k with k Hk,
  unfold fin.shift fin.nest fin.split,
  { have H : ¬ m + k < m,
    { apply not_lt_of_ge, apply le_add_right },
    rw [dif_neg H],
    apply congr_arg,
    apply fin.eq_of_veq,
    unfold fin.val,
      -- simp, below, invokes two similar lemmas for the
      -- stability of the proof
    simp [nat.add_sub_cancel_left,nat.add_sub_cancel] },
end

lemma fin.split_unsplit {n m : ℕ} (k : fin m ⊕ fin n)
: fin.split (fin.unsplit k) = k :=
begin
  cases k with k k
  ; unfold fin.unsplit,
  { rw fin.split_nest },
  { rw fin.split_shift },
end

lemma fin.unsplit_split {n m : ℕ} (k : fin (m + n))
: fin.unsplit (fin.split k) = k :=
begin
  cases k with k Hk,
  cases classical.em (k < m) with h h
  ; unfold fin.split,
  { rw dif_pos h, unfold fin.unsplit fin.nest, },
  { rw dif_neg h,
    apply fin.eq_of_veq,
    unfold fin.unsplit fin.shift fin.val,
    rw [← nat.add_sub_assoc,nat.add_sub_cancel_left],
    apply le_of_not_gt h },
end

lemma fin.unsplit_eq_iff_eq_split {n m : ℕ} (p : fin m ⊕ fin n) (q : fin (m + n))
: fin.unsplit p = q ↔ p = fin.split q :=
begin
  split ; intro h,
  { rw [← h,fin.split_unsplit], },
  { rw [h,fin.unsplit_split], },
end

lemma fin.nest_eq_iff_eq_split {n m : ℕ} (p : fin m) (q : fin (m + n))
: fin.nest p = q ↔ sum.inl p = fin.split q :=
by { rw ← fin.unsplit_eq_iff_eq_split, refl }

lemma fin.shift_eq_iff_eq_split {n m : ℕ} (p : fin n) (q : fin (m + n))
: fin.shift p = q ↔ sum.inr p = fin.split q :=
by { rw ← fin.unsplit_eq_iff_eq_split, refl }

lemma fin.split_injective  {n m : ℕ} (p q : fin (m + n))
  (h : fin.split p = fin.split q)
: p = q :=
by { rw [← fin.unsplit_eq_iff_eq_split,fin.unsplit_split] at h, assumption }

lemma fin.val_shift_zero (m n : ℕ)
: (@fin.shift _ m (0 : fin (succ n))).val = m :=
rfl

lemma fin.shift_zero (m : ℕ)
: fin.max = (@fin.shift _ m (0 : fin 1)) :=
begin
  apply fin.eq_of_veq,
  unfold fin.shift fin.max, simp [fin.val_shift_zero],
end

lemma fin.val_of_nat {m n : ℕ} (h : n < nat.succ m)
: (@fin.of_nat m n).val = n :=
begin
  unfold fin.of_nat fin.val,
  rw mod_eq_of_lt h
end

def fin.foldl {n : ℕ}
  (f : α → β → β) (x : β) (a : fin n → α) : β :=
(array.mk a).foldl x f

def fin.sum (n : ℕ)
  [has_add α] [has_zero α]
  (a : fin n → α) : α :=
fin.foldl has_add.add 0 a
