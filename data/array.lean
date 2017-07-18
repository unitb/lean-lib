
import util.data.fin
import util.data.order

universe variables u₀ u₁ u₂
variables {α : Type u₀} {β β' : Type u₁} {γ : Type u₂}

open nat

namespace array

def push_aux {n : ℕ} (x : α) (ar : fin n → α) : fin (succ n) → α
  | ⟨0,_⟩ := x
  | ⟨succ i,P⟩ := ar ⟨i,lt_of_succ_lt_succ P⟩

def push {n : ℕ} (x : α) : array α n → array α (succ n)
  | ⟨ ar ⟩ := ⟨ push_aux x ar ⟩

def pop {n : ℕ} : array α (succ n) → array α n
  | ⟨ ar ⟩ := ⟨ ar ∘ fin.succ ⟩

def head {n : ℕ} : array α (succ n) → α
  | ⟨ ar ⟩ := ar 0

lemma push_head_pop {n : ℕ} (xs : array α (succ n))
: push (head xs) (pop xs) = xs := sorry

lemma rev_iterate_push {n : ℕ}
  (x : α) (xs : array α n)
  (i : β)
  (f : fin (succ n) → α → β → β)
: rev_iterate (push x xs) i f = f 0 x (rev_iterate xs i (f ∘ fin.succ)) :=
begin
  revert x xs,
  induction n with n IH ; intros x xs,
  { cases xs with xs,
    unfold push push_aux rev_iterate rev_iterate_aux,
    simp,
    unfold read data push_aux,
    rw fin.zero_def', refl },
  { rw [← push_head_pop xs,IH],
    unfold function.comp,
    rw push_head_pop xs,
    admit }
end

def maximum_aux {n : ℕ} (a : array ℕ n) (i : ℕ) (H : i ≤ n) : ℕ :=
array.iterate_aux a (λ _, max) i H 0

lemma le_maximum_aux {n : ℕ} (a : array ℕ n) (k : ℕ) (Hk : k ≤ n)
  (i  : fin n)
  (Hi : i.val < k)
: a.read i ≤ maximum_aux a k Hk :=
begin
  induction k,
  case nat.zero { admit },
  case nat.succ k
  { unfold maximum_aux iterate_aux,
    simp, admit },
end

def maximum {n : ℕ} (a : array ℕ n) : ℕ :=
maximum_aux a n (by refl)

lemma le_maximum {n : ℕ} (a : array ℕ n) (i : fin n)
: a.read i ≤ maximum a :=
begin
  apply le_maximum_aux,
  apply i.is_lt
end

lemma rev_list_eq_nil (ar : array α 0)
: ar.rev_list = [] :=
by refl

lemma to_list_eq_nil (ar : array α 0)
: ar.to_list = [] :=
by refl

lemma iterate_aux_pop {n : ℕ} (ar : array α (succ n))
  (f : fin (succ n) → α → β → β) (x : β)
  {k : ℕ}
  (Hk : k ≤ n)
: iterate_aux ar f (succ k) (succ_le_succ Hk) x
= iterate_aux (pop ar) (f ∘ fin.succ) k Hk (f 0 (ar.read 0) x) :=
begin
  induction k,
  case zero
    { refl },
  case succ k
    { rw array.iterate_aux.equations._eqn_2 (pop ar), simp,
      rw ← ih_1, unfold iterate_aux, simp,
      apply congr_fun,
      cases ar, refl }
end

lemma rev_list_eq_cons_aux {n k : ℕ} (ar : array α n) (xs : list α)
  (H : k ≤ n)
: iterate_aux ar (λ _, list.cons) k H xs =
      iterate_aux ar (λ _, list.cons) k H [] ++ xs :=
begin
  induction k,
  { unfold iterate_aux, simp },
  { unfold iterate_aux, simp [ih_1], },
end

lemma rev_list_eq_cons {n : ℕ} (ar : array α (succ n))
: ar.rev_list = ar.pop.rev_list ++ [ar.read 0] :=
begin
  unfold rev_list foldl iterate,
  rw [iterate_aux_pop _ _ _ (le_refl n),rev_list_eq_cons_aux],
end

lemma iterate_aux_pop_back {n : ℕ} (ar : array α (succ n))
  (f : fin (succ n) → α → β → β) (x : β)
  (k : ℕ)
  (Hk : k ≤ n)
: iterate_aux ar f k (le_succ_of_le Hk) x = iterate_aux (pop_back ar) (restr f) k Hk x :=
begin
  induction k,
  case zero
    { refl },
  case succ k
    { unfold iterate_aux, simp,
      apply congr_arg,
      apply ih_1 },
end

lemma rev_list_eq_append {n : ℕ} (ar : array α (succ n))
: ar.rev_list = ar.read fin.max :: ar.pop_back.rev_list :=
begin
  unfold rev_list foldl iterate iterate_aux,
  simp,
  apply congr_arg,
  apply iterate_aux_pop_back,
end

end array

lemma fin.sum_zero
  [has_add α] [has_zero α]
  (f : fin 0 → α)
: fin.sum 0 f = 0 :=
begin
  unfold fin.sum fin.foldl,
  rw [array.foldl_eq,array.rev_list_eq_nil],
  refl,
end

lemma fin.sum_succ {n : ℕ}
  [add_comm_monoid α]
  (f : fin (succ n) → α)
: fin.sum (succ n) f = fin.sum n (f ∘ fin.succ) + f 0 :=
begin
  unfold fin.sum fin.foldl,
  simp [array.foldl_eq,array.rev_list_eq_cons],
  unfold array.read array.data array.pop,
  rw list.append_foldr,
  unfold list.foldr,
  symmetry,
  apply list.foldr_hom (has_add.add (f 0)) has_add.add has_add.add 0 _ _,
  intros, ac_refl
end

lemma fin.sum_succ' {n : ℕ}
  [add_comm_monoid α]
  (f : fin (succ n) → α)
: fin.sum (succ n) f = fin.sum n (f ∘ widen) + f fin.max :=
begin
  unfold fin.sum fin.foldl,
  rw [array.foldl_eq,array.foldl_eq,array.rev_list_eq_append],
  unfold list.foldr array.read array.data,
  rw [add_comm],
  apply congr_fun,
  apply congr_arg,
  apply congr_arg,
  apply congr_arg,
  unfold array.pop_back,
  apply congr_arg,
  apply funext, intro, cases x with i Hi,
  refl,
end
