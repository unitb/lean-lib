
namespace nat

theorem lt_of_not_le {m n : ℕ} (h : ¬ m ≤ n) : n < m :=
begin
  cases lt_or_ge n m with h' h',
  { apply h' },
  { cases h h' }
end

theorem mod_of_lt {m n : ℕ} (h : n > m) : m % n = m :=
begin
  rw [nat.mod_def,if_neg],
  intro h',
  cases h' with h₀ h₁,
  apply not_le_of_gt h h₁,
end

theorem mod_mod (m n : ℕ) : (m % n) % n = m % n :=
begin
  cases lt_or_eq_of_le (zero_le n) with h h,
  { apply mod_of_lt, apply mod_lt _ h },
  { subst n, rw [mod_def,if_neg],
    intro h', apply lt_irrefl _ h'.left }
end

theorem mod_plus (n p : ℕ) (h : p > 0) : ∃k q, q < p ∧ n = k * p + q :=
begin
  existsi (n / p), existsi (n % p),
  split,
  { apply mod_lt _ h, },
  { simp [mod_add_div] }
end

theorem mul_plus_mod (k p q : ℕ) (h : q < p) : (k * p + q) % p = q :=
begin
  induction k with k,
  { rw [mod_def,if_neg], simp,
    simp, intro h', apply not_lt_of_ge h'^.left h },
  { rw [mod_def,if_pos,succ_mul],
    simp [nat.add_sub_cancel_left],
    simp at ih_1,
    apply ih_1,
    { split,
      { apply lt_of_le_of_lt (zero_le _), apply h },
      { simp [succ_mul], apply nat.le_add_right  } } }
end

theorem succ_mod' {n p : ℕ} (h : succ (n % p) < p) : succ n % p = succ (n % p) :=
begin
   have h₁ : p > 0,
   { apply lt_of_le_of_lt (zero_le _), apply h },
   have h₀ := mod_plus n p h₁,
   cases h₀ with k h₀, cases h₀ with q h₀,
   cases h₀ with h₀ h₁,
   subst n,
   rw mul_plus_mod _ _ _ h₀ at h,
   rw [-add_succ,mul_plus_mod _ _ _ h₀,mul_plus_mod _ _ _ h],
end

theorem succ_mod (n p : ℕ) : succ n % p = succ (n % p) % p :=
begin
  symmetry,
  cases decidable.em (0 < p) with h₂ h₂,
  cases decidable.em (p ≤ succ (n % p)) with h₃ h₃,
  { have h' : succ (n % p) = p,
    { apply le_antisymm _ h₃,
      { apply mod_lt _ h₂ } },
    cases mod_plus n p h₂  with k h₀,
    cases h₀ with q h₀,
    cases h₀ with h₀ h₁,
    rw [mod_def,if_pos (and.intro h₂ h₃),h',nat.sub_self,zero_mod],
    subst n, rw [mul_plus_mod _ _ _ h₀] at h',
    have h₁ : k * p + succ q = (k+1) * p + 0,
    { rw h', simp [add_mul] },
    rw [-add_succ, h₁, mul_plus_mod _ _ _ h₂], },
  { have h₀ := lt_of_not_ge h₃,
    rw [succ_mod' h₀,succ_mod',mod_mod],
    { rw mod_mod, apply h₀ }  },
  { have h'' := le_antisymm (zero_le _) (le_of_not_gt h₂),
    subst p, simp [nat.mod_zero] },
end

theorem mod_add' {m n p : ℕ} : (m + n) % p = (m + n % p) % p :=
begin
  induction m with m,
  { symmetry, simp, apply mod_mod },
  { rw [succ_add,succ_mod,ih_1,succ_add,-succ_mod] }
end

theorem mod_add {m n p : ℕ} : (m + n) % p = (m % p + n % p) % p :=
begin
  rw [mod_add',nat.add_comm,mod_add',nat.add_comm]
end

theorem nat.mod_self' {m : ℕ} : m % m = 0 :=
begin
  rw [mod_def],
  cases decidable.em (0 < m) with h h,
  { have h' := and.intro h (nat.le_refl m),
    rw [if_pos h',nat.sub_self,zero_mod] },
  { have h' : ¬ (0 < m ∧ m ≤ m),
    { intro h', apply h,
      cases h' with h₀ h₁,
      apply h₀ },
    rw [if_neg h'],
    apply le_antisymm _ (zero_le _),
    apply le_of_not_gt h },
end

theorem lt_of_pred_lt {m n : ℕ}
  (h : m < pred n)
: m < n :=
begin
  cases n with n
  ; unfold pred at h,
  { apply h },
  { apply nat.le_trans h (le_succ _), },
end

theorem lt_pred_of_lt {m n : ℕ}
  (h : m < n)
: pred m < n :=
begin
  cases m with m,
  { apply h },
  { apply nat.lt_trans _ h,
    apply lt_succ_self }
end

theorem succ_pred_le_self (x : ℕ)
: x ≤ succ (pred x) :=
begin
  cases x with x,
  { apply zero_le },
  { apply succ_le_succ,
    refl },
end

lemma pred_lt_self_of_pos : ∀ {v : ℕ},
  0 < v → pred v < v
| 0 p := absurd p (not_lt_zero _)
| (succ n) _ := lt_succ_self _


protected lemma sub_lt_sub_right {m n p : ℕ}
  (h₀ : p ≤ m)
  (h₁ : m < n)
: m - p < n - p :=
begin
  induction p with p IH,
  { apply h₁ },
  { simp [sub_succ],
    have Hmp : m - p ≠ 0,
    { apply ne_of_gt,
      apply nat.sub_pos_of_lt h₀ },
    have Hnp : n - p ≠ 0,
    { apply ne_of_gt,
      apply nat.sub_pos_of_lt,
      apply nat.lt_trans h₀ h₁  },
    apply pred_lt_pred Hmp Hnp,
    apply IH,
    apply le_trans _ h₀,
    apply le_succ }
end

protected lemma sub_lt_sub_left {m p q : ℕ}
  (h₀ : p ≤ m)
  (h₁ : q < p)
: m - p < m - q :=
begin
  apply lt_of_succ_le,
  rw -succ_sub h₀,
  cases p with p,
  { cases not_lt_zero _ h₁ },
  { rw succ_sub_succ,
    apply nat.sub_le_sub_left,
    apply le_of_succ_le_succ h₁ },
end

protected lemma sub_le_sub {m n p q : ℕ}
  (h₀ : m ≤ n)
  (h₁ : q ≤ p)
: m - p ≤ n - q :=
begin
  transitivity n - p,
  apply nat.sub_le_sub_right h₀,
  apply nat.sub_le_sub_left _ h₁
end

protected lemma mul_add_mod_self_left
  (x y k : ℕ)
  (h : k < x)
: (x * y + k) % x = k :=
by simp [mod_eq_of_lt h]

lemma div_lt_of_lt_mul (x : ℕ) {m n : ℕ} (h : x < m * n) : x / n < m :=
begin
  have hmn : 0 < m * n,
  { apply lt_of_le_of_lt _ h,
    apply nat.zero_le },
  have hn : 0 < n,
  { apply pos_of_mul_pos_left hmn,
    apply nat.zero_le, },
  clear hmn,
  revert x,
  induction m with m ; intros x h,
  { simp at h, cases not_lt_zero _ h },
  { cases (lt_or_ge x n) with h' h',
    { rw [div_eq_of_lt h'], apply zero_lt_succ },
    { rw [div_eq_sub_div hn h',nat.add_one_eq_succ],
      apply succ_lt_succ,
      apply ih_1,
      apply @nat.lt_of_add_lt_add_left n,
      rw [-nat.add_sub_assoc h',nat.add_sub_cancel_left],
      simp [succ_mul] at h, simp [h],  } }
end

protected lemma mul_add_div_self_left (x y k : ℕ) (h : k < x)
: (x * y + k) / x = y :=
begin
  have h₀ : x > 0,
  { apply lt_of_le_of_lt (zero_le _) h },
  simp,
  induction y with y,
  { simp [div_eq_of_lt h] },
  { rw [mul_succ,div_eq_sub_div h₀],
    { simp [nat.add_sub_cancel_left,add_one_eq_succ],
      apply congr_arg,
      apply eq.trans _ ih_1,
      simp },
    { simp, apply le_add_right } }
end

protected lemma add_mul_div_self_right {a} b {n : ℕ} (h : a < n)
: (a + b * n) / n = b :=
by rw [add_comm,mul_comm,nat.mul_add_div_self_left _ _ _ h]

protected lemma mul_lt_mul {a b c d : ℕ}
  (h₀ : a < c)
  (h₁ : b < d)
: a * b < c * d :=
begin
  revert a,
  induction c with c ; intros a h₀,
  { cases (nat.not_lt_zero _ h₀) },
  cases a with a,
  { rw [nat.succ_mul],
    apply lt_of_lt_of_le,
    simp, apply lt_of_le_of_lt (zero_le b), apply h₁,
    apply le_add_left  },
  { rw [succ_mul,succ_mul],
    apply add_lt_add,
    apply ih_1,
    apply lt_of_succ_lt_succ h₀,
    apply h₁, }
end

end nat
