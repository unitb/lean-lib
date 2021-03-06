
import data.nat.basic
import data.nat.modeq
import util.data.nat
import algebra.group_power
import tactic.find
open nat

-- lemma mod_mod (n m : ℕ)
-- : n % m % m = n % m :=
-- sorry

@[simp]
lemma mod_add_mod (n m p : ℕ)
: (n % p + m) % p = (n + m) % p :=
by apply int.coe_nat_inj ; simp

@[simp]
lemma add_mod_mod (n m p : ℕ)
: (n + m % p) % p = (n + m) % p :=
by apply int.coe_nat_inj ; simp

@[simp]
lemma mul_mod_mod (n m p : ℕ)
: n * (m % p) % p = (n * m) % p :=
begin
  induction n ; simp [succ_mul],
  rw [← add_mod_mod], simp [n_ih],
end

@[simp]
lemma mod_mul_mod (n m p : ℕ)
: (n % p) * m % p = (n * m) % p :=
by simp [mul_comm]

instance (n : ℕ) : monoid (fin (succ n)) :=
begin
 refine { mul := fin.mul
        , one := 1
        , .. }
 ; intros ;
 casesm* fin _ ;
 apply fin.eq_of_veq ;
 simp! [mul_assoc,mod_eq_of_lt,*],
end
