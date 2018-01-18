
import util.data.nat

open nat (hiding zero_le)
open list

def fin_interleave (n : ℕ) (i : ℕ) : fin (succ n) :=
⟨i % succ n,mod_lt _ (succ_le_succ $ nat.zero_le _)⟩

theorem inf_repeat_fin_inter {n : ℕ} : ∀ x i, ∃ j, fin_interleave n (i+j) = x :=
begin
  intro x,
  cases x with x H,
  intro i,
  existsi x + succ n - (i % succ n),
  tactic.swap,
  unfold fin_interleave,
  have h : i % succ n ≤ succ n,
  { apply nat.le_of_lt (mod_lt _ _),
    apply succ_le_succ, apply nat.zero_le },
  apply fin.eq_of_veq, unfold fin.val ,
  rw [nat.add_sub_assoc h,add_comm x,← add_assoc,mod_add,@mod_add i],
  rw [← @mod_add' (i % succ n),← nat.add_sub_assoc h],
  rw [nat.add_sub_cancel_left, nat.mod_self',nat.zero_add,mod_mod,mod_of_lt],
  apply H,
end
