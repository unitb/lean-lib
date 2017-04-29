
open nat

instance {n : ℕ} : inhabited (fin (succ n)) :=
inhabited.mk ⟨n,lt_succ_self _⟩

lemma fin.zero_def (n : ℕ)
: (0 : fin (succ n)).val = 0 :=
begin
  unfold zero has_zero.zero fin.of_nat fin.val,
  apply mod_eq_of_lt,
  apply zero_lt_succ
end

def fin.pred {n} : fin n → fin n
  | ⟨i,P⟩ := ⟨pred i,lt_of_le_of_lt (pred_le _) P⟩

def fin.succ {n} : fin n → fin n
  | ⟨i,P⟩ := if P' : succ i < n then ⟨succ i,P'⟩
                                else ⟨i,P⟩

lemma fin.val_succ_le_nat_succ {n : ℕ} (x : fin n)
: x.succ.val ≤ succ (x.val) :=
begin
  cases n with n
  ; cases x with x Pn
  ; unfold fin.succ fin.val,
  { cases not_lt_zero _ Pn },
  cases decidable.em (succ x < succ n) with h h,
  { rw dif_pos h },
  { rw dif_neg h,
    apply le_succ },
end

lemma fin.pred_def {n : ℕ} (x : fin n)
: (x.pred).val = pred x.val :=
begin
  cases x with x Px,
  refl
end

lemma fin.succ_def  {n : ℕ} (x : fin n)
  (h : succ x.val < n)
: (x.succ).val = succ x.val :=
begin
  cases x with x Px,
  unfold fin.succ fin.val,
  unfold fin.val at h,
  rw dif_pos h,
end

def fin.max {n} : fin (succ n) := ⟨n,lt_succ_self _⟩

lemma fin.max_def {n}
: (@fin.max n).val = n := rfl

lemma fin.pred_succ {n} (x : fin n)
  (h : succ x.val < n)
: x.succ.pred = x :=
begin
  apply fin.eq_of_veq,
  rw [fin.pred_def,fin.succ_def,pred_succ],
  apply h,
end

lemma fin.succ_pred {n} (x : fin (succ n))
  (h : 0 < x)
: x.pred.succ = x :=
begin
  apply fin.eq_of_veq,
  assert h' : 0 < x.val,
  { rw [fin.lt_def,fin.zero_def] at h,
    apply h },
  rw [fin.succ_def,fin.pred_def,succ_pred_eq_of_pos h'],
  rw [fin.pred_def,succ_pred_eq_of_pos h'],
  apply x.is_lt,
end

lemma fin.succ_le_self {n} (x : fin (succ n))
  (h : x < fin.max)
: ¬ x.succ ≤ x :=
begin
  rw [fin.le_def,fin.succ_def],
  apply not_succ_le_self,
  apply succ_lt_succ,
  rw [fin.lt_def,fin.max_def] at h,
  apply h
end

lemma fin.le_succ_self {n} (x : fin (succ n))
: x ≤ x.succ :=
begin
  cases x with x Px,
  unfold fin.succ,
  cases decidable.em (succ x < succ n) with h h,
  { rw [dif_pos h,fin.le_def],
    apply le_succ },
  { rw [dif_neg h,fin.le_def], },
end
