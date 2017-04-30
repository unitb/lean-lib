
import util.data.bijection

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
  cases decidable.em (n > 0) with h h,
  { apply mod_of_lt, apply mod_lt _ h },
  { note h' := le_antisymm (zero_le _) (le_of_not_gt h),
    subst n, rw [mod_def,if_neg],
    intro h', apply h,
    cases h' with h₀ h₁, apply h₀ }
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
   assert h₁ : p > 0,
   { apply lt_of_le_of_lt (zero_le _), apply h },
   note h₀ := mod_plus n p h₁,
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
  { assert h' : succ (n % p) = p,
    { apply le_antisymm _ h₃,
      { apply mod_lt _ h₂ } },
    cases mod_plus n p h₂  with k h₀,
    cases h₀ with q h₀,
    cases h₀ with h₀ h₁,
    rw [mod_def,if_pos (and.intro h₂ h₃),h',nat.sub_self,zero_mod],
    subst n, rw [mul_plus_mod _ _ _ h₀] at h',
    assert h₁ : k * p + succ q = (k+1) * p + 0,
    { rw h', simp [add_mul] },
    rw [-add_succ, h₁, mul_plus_mod _ _ _ h₂], },
  { note h₀ := lt_of_not_ge h₃,
    rw [succ_mod' h₀,succ_mod',mod_mod],
    { rw mod_mod, apply h₀ }  },
  { note h'' := le_antisymm (zero_le _) (le_of_not_gt h₂),
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
  { note h' := and.intro h (nat.le_refl m),
    rw [if_pos h',nat.sub_self,zero_mod] },
  { assert h' : ¬ (0 < m ∧ m ≤ m),
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

end nat
