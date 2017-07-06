
import util.data.fin
import util.data.order

universe variables u₀ u₁ u₂
variables {α : Type u₀} {β β' : Type u₁} {γ : Type u₂}

namespace array

open nat

def push_aux {n : ℕ} (x : α) (ar : fin n → α) : fin (succ n) → α
  | ⟨0,_⟩ := x
  | ⟨succ i,P⟩ := ar ⟨i,lt_of_succ_lt_succ P⟩

def push {n : ℕ} (x : α) : array α n → array α (succ n)
  | ⟨ ar ⟩ := ⟨ push_aux x ar ⟩

def pop {n : ℕ} : array α (succ n) → array α n
  | ⟨ ar ⟩ := ⟨ ar ∘ fin.next ⟩

def head {n : ℕ} : array α (succ n) → α
  | ⟨ ar ⟩ := ar 0

lemma push_head_pop {n : ℕ} (xs : array α (succ n))
: push (head xs) (pop xs) = xs := sorry

lemma rev_iterate_push {n : ℕ}
  (x : α) (xs : array α n)
  (i : β)
  (f : fin (succ n) → α → β → β)
: rev_iterate (push x xs) i f = f 0 x (rev_iterate xs i (f ∘ fin.next)) :=
begin
  revert x xs,
  induction n with n IH ; intros x xs,
  { cases xs with xs,
    unfold push push_aux rev_iterate rev_iterate_aux,
    simp,
    unfold read data push_aux,
    rw fin.zero_def', refl },
  { rw [-push_head_pop xs,IH],
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

end array
