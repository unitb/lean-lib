
open nat

lemma fin.zero_def (n : ℕ) : (0 : fin (succ n)).val = 0 := sorry

def fin.pred {n} : fin n → fin n
  | ⟨i,P⟩ := ⟨pred i,lt_of_le_of_lt (pred_le _) P⟩

def fin.succ {n} : fin n → fin n
  | ⟨i,P⟩ := if P' : succ i < n then ⟨succ i,P'⟩
                                else ⟨i,P⟩

lemma fin.val_succ_le_nat_succ {n : ℕ} (x : fin n)
: x.succ.val ≤ succ (x.val) := sorry

lemma fin.pred_def {n : ℕ} (x : fin n)
: (x.pred).val = pred x.val := sorry

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

lemma fin.pred_succ {n} (x : fin (succ n))
  (h : x.val < n)
: x.succ.pred = x := sorry

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
: ¬ x.succ ≤ x := sorry

lemma fin.le_succ_self {n} (x : fin (succ n))
: x ≤ x.succ := sorry
