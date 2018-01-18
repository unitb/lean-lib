
import data.list
import data.list.basic
import data.array.lemmas
import util.data.fin
import util.data.list
import util.data.order
import util.meta.tactic

universe variables u₀ u₁ u₂
variables {α : Type u₀} {β β' : Type u₁} {γ : Type u₂}

open nat (hiding foldr)

namespace array

def push_aux {n : ℕ} (x : α) (ar : fin n → α) : fin (succ n) → α
  | ⟨0,_⟩ := x
  | ⟨succ i,P⟩ := ar ⟨i,lt_of_succ_lt_succ P⟩

def push {n : ℕ} (x : α) : array n α → array (succ n) α
  | ⟨ ar ⟩ := ⟨ push_aux x ar ⟩

def pop {n : ℕ} : array (succ n) α → array n α
  | ⟨ ar ⟩ := ⟨ ar ∘ fin.succ ⟩

def head {n : ℕ} : array (succ n) α → α
  | ⟨ ar ⟩ := ar 0

lemma push_head_pop {n : ℕ} (xs : array (succ n) α)
: push (head xs) (pop xs) = xs := sorry

open d_array -- (rev_iterate_aux rev_iterate)
lemma rev_iterate_push {n : ℕ}
  (x : α) (xs : array n α)
  (i : β)
  (f : fin (succ n) → α → β → β)
: rev_iterate (push x xs) i f = f 0 x (rev_iterate xs i (f ∘ fin.succ)) :=
begin
  revert x xs,
  induction n with n IH ; intros x xs,
  { cases xs with xs, refl, },
  { rw [← push_head_pop xs,IH],
    unfold function.comp,
    rw [push_head_pop xs],
    admit }
end

def maximum_aux {n : ℕ} (a : array n ℕ) (i : ℕ) (H : i ≤ n) : ℕ :=
d_array.iterate_aux a (λ _, max) i H 0

lemma le_maximum_aux {n : ℕ} (a : array n ℕ) (k : ℕ) (Hk : k ≤ n)
  (i  : fin n)
  (Hi : i.val < k)
: a.read i ≤ maximum_aux a k Hk :=
begin
  induction k,
  case nat.zero { admit },
  case nat.succ : k
  { unfold maximum_aux iterate_aux,
    simp, admit },
end

def maximum {n : ℕ} (a : array n ℕ) : ℕ :=
maximum_aux a n (by refl)

lemma le_maximum {n : ℕ} (a : array n ℕ) (i : fin n)
: a.read i ≤ maximum a :=
begin
  apply le_maximum_aux,
  apply i.is_lt
end

lemma rev_list_eq_nil (ar : array 0 α)
: ar.rev_list = [] :=
by refl

lemma to_list_eq_nil (ar : array 0 α)
: ar.to_list = [] :=
by refl

lemma iterate_aux_pop {n : ℕ} (ar : array (succ n) α)
  (f : fin (succ n) → α → β → β) (x : β)
  {k : ℕ}
  (Hk : k ≤ n)
: iterate_aux ar f (succ k) (succ_le_succ Hk) x
= iterate_aux (pop ar) (f ∘ fin.succ) k Hk (f 0 (ar.read 0) x) :=
begin
  induction k,
  case zero
    { refl },
  case succ : k
    { rw d_array.iterate_aux.equations._eqn_2 (pop ar), simp,
      rw ← k_ih, unfold iterate_aux, simp,
      apply congr_fun,
      cases ar, refl }
end

lemma rev_list_eq_cons_aux {n k : ℕ} (ar : array n α) (xs : list α)
  (H : k ≤ n)
: iterate_aux ar (λ _, list.cons) k H xs =
      iterate_aux ar (λ _, list.cons) k H [] ++ xs :=
begin
  induction k,
  { unfold iterate_aux, simp },
  { unfold iterate_aux, simp [k_ih], },
end

lemma rev_list_eq_cons {n : ℕ} (ar : array (succ n) α)
: ar.rev_list = ar.pop.rev_list ++ [ar.read 0] :=
begin
  unfold rev_list foldl iterate d_array.iterate,
  rw [iterate_aux_pop _ _ _ (le_refl n),rev_list_eq_cons_aux],
end

lemma iterate_aux_pop_back {n : ℕ} (ar : array (succ n) α)
  (f : fin (succ n) → α → β → β) (x : β)
  (k : ℕ)
  (Hk : k ≤ n)
: iterate_aux ar f k (le_succ_of_le Hk) x = iterate_aux (pop_back ar) (restr f) k Hk x :=
begin
  induction k,
  case zero
    { refl },
  case succ : k
    { unfold iterate_aux, simp,
      apply congr_arg,
      apply k_ih },
end

lemma rev_list_eq_append {n : ℕ} (ar : array (succ n) α)
: ar.rev_list = ar.read fin.max :: ar.pop_back.rev_list :=
begin
  unfold rev_list foldl iterate d_array.iterate iterate_aux,
  simp, split, refl,
  apply iterate_aux_pop_back,
end

end array

lemma fin.sum_zero
  [has_add α] [has_zero α]
  (f : fin 0 → α)
: fin.sum 0 f = 0 :=
rfl
open array
lemma fin.sum_succ {n : ℕ}
  [add_comm_monoid α]
  (f : fin (succ n) → α)
: fin.sum (succ n) f = fin.sum n (f ∘ fin.succ) + f 0 :=
begin
  unfold fin.sum fin.foldl,
  repeat { rw [← rev_list_foldr] },
  simp [d_array.foldl,array.rev_list_eq_cons,d_array.iterate,d_array.iterate_aux
       ,read,d_array.read,d_array.data,array.pop],
  symmetry,
  rw list.foldr_hom (has_add.add (f 0)), simp,
  intros, simp
end

@[simp]
lemma array_widen_eq_pop_back {n : ℕ} (f : fin (succ n) → α)
: d_array.mk (f ∘ widen) = array.pop_back ⟨f⟩ :=
begin
  ext1, cases i, refl,
end

open list
lemma fin.sum_succ' {n : ℕ}
  [add_comm_monoid α]
  (f : fin (succ n) → α)
: fin.sum (succ n) f = fin.sum n (f ∘ widen) + f fin.max :=
begin
  unfold fin.sum fin.foldl,
  rw [← to_list_foldl,← to_list_foldl],
  simp [foldl_eq_foldr',rev_list_eq_append,foldr,flip,read,d_array.read],
end
