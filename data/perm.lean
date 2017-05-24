
import util.data.bijection

import util.logic
import util.data.fin
import util.data.nat

namespace bijection

universe variables u

variables  {α : Type u}

def swap' [decidable_eq α] (i j k : α) : α :=
if i = k then j
else if j = k then i
else k

def by_symmetry {α} {P Q : α → α → Prop}
  (h₁ : ∀ x y, Q x y ↔ Q y x)
  (h₂ : ∀ x y, P x y → Q x y)
  (x y : α)
  (h₀ : P x y ∨ P y x)
: Q x y :=
begin
  cases h₀ with h₀ h₀,
  { apply h₂ _ _ h₀ },
  { rw h₁, apply h₂ _ _ h₀ },
end

def swap_left [decidable_eq α] (i j : α)
: swap' i j i = j :=
begin
  unfold swap',
  simp
end

def swap_neq [decidable_eq α] {i j k : α}
  (h : ¬ (i = k ∨ j = k))
: swap' i j k = k :=
begin
  rw [not_or_iff_not_and_not] at h,
  cases h with hi hj,
  unfold swap',
  rw [if_neg hi,if_neg hj],
end

def swap_symmetry' [decidable_eq α] (i j : α)
: swap' i j = swap' j i :=
begin
  apply funext, intro k,
  unfold swap',
  cases decidable.em (i = k) with Hi Hi,
  { rw if_pos Hi,
    cases decidable.em (j = k) with Hj Hj,
    { rw if_pos Hj, subst i, apply Hj },
    { rw [if_neg Hj,if_pos], apply Hi } },
  { rw if_neg Hi,
    cases decidable.em (j = k) with Hj Hj,
    { rw [if_pos Hj,if_pos Hj], },
    { rw [if_neg Hj,if_neg Hj,if_neg Hi], } },
end

def swap_right [decidable_eq α] (i j : α)
: swap' i j j = i :=
by rw [swap_symmetry',swap_left]

def swap_inverse' [decidable_eq α] (i j k : α)
: swap' i j (swap' i j k) = k :=
begin
  cases decidable.em (i = k ∨ j = k) with h h,
  { revert i j,
    apply by_symmetry ; intros i j,
    { rw swap_symmetry' },
    intro h,
    subst i,
    rw [swap_left,swap_right] },
  { simp [swap_neq h] }
end

def swap [decidable_eq α] (i j : α) : bijection α α :=
bijection.mk (swap' i j) (swap' i j) (swap_inverse' i j) (swap_inverse' i j)

@[simp]
lemma swap_f [decidable_eq α] (i j : α)
: (swap i j).f = swap' i j := rfl

@[simp]
lemma swap_g [decidable_eq α] (i j : α)
: (swap i j).g = swap' i j := rfl

lemma swap_inverse [decidable_eq α] (i j : α)
: swap i j ∘ swap i j = id :=
begin
  apply bijection.eq
  ; intro x
  ; simp [comp_f,comp_g]
  ; unfold function.comp
  ; simp [swap_inverse']
  ; refl
end

lemma swap_symmetry [decidable_eq α] (i j : α)
: swap i j = swap j i :=
begin
  apply bijection.eq
  ; intro x
  ; simp [comp_f,comp_g]
  ; unfold function.comp
  ; simp [swap_symmetry']
end

open list nat

-- protected def to_list' {α} : ∀ {n : ℕ} (k : fin n → α), list α
--   | 0 f := nil
--   | (succ n) f := f 0 :: @to_list' n (f ∘ fin.succ)

-- def to_list {n : ℕ} {α} (b : bijection (fin n) α) : list α :=
-- bijection.to_list' b.f

-- protected lemma length_to_list' {n : ℕ} (x : bijection (fin n) α)
-- : length (bijection.to_list' x.f) = n :=
-- begin
--   generalize x.f f, clear x,
--   induction n with n IH ; intro f,
--   { refl },
--   { unfold bijection.to_list',
--     simp [add_one_eq_succ,IH], },
-- end

-- lemma length_to_list {n : ℕ} (x : bijection (fin n) α) : length x.to_list = n :=
-- bijection.length_to_list' x

end bijection

def perm (n : ℕ) := bijection (fin n) (fin n)

-- def fin.succ {n : ℕ} : fin n → fin (nat.succ n)
--   | ⟨m,p⟩ := ⟨nat.succ m,nat.succ_lt_succ p⟩

namespace perm

universe variables u

variables {n : ℕ} {α : Type u}

open list nat bijection

@[reducible]
def id : perm n := bijection.id

lemma left_id {α} (x : bijection α (fin n)) : id ∘ x = x :=
bijection.left_id x

lemma right_id {β} (x : bijection (fin n) β) : x ∘ id = x :=
bijection.right_id x

-- @[reducible]
-- def to_list : perm n → list (fin n) := bijection.to_list

-- def rotate_left' : ∀ k, k < n → perm n
--   | 0 Pk := id
--   | (succ k) Pk := rotate_left' k (lt_of_succ_lt Pk) ∘ swap ⟨k,lt_of_succ_lt Pk⟩ ⟨succ k,Pk⟩

-- def rotate_right' : ∀ k, k < n → perm n
--   | 0 Pk := id
--   | (succ k) Pk :=
--     have Hsucc_succ_k : n - succ (succ k) < n,
--          begin
--            apply sub_lt_of_pos_le,
--            apply zero_lt_succ,
--            apply Pk,
--          end,
--     have Hsucc_k : n - succ k < n,
--          begin
--            apply sub_lt_of_pos_le,
--            apply zero_lt_succ,
--            apply le_of_lt Pk,
--          end,
--       rotate_right' k (lt_of_succ_lt Pk) ∘ swap ⟨n - succ k,Hsucc_k⟩ ⟨n - succ (succ k),Hsucc_succ_k⟩

-- lemma rotate_left_gt_eq_self {n : ℕ} (k : ℕ) (P : k < n) (i : fin n)
--   (h : k < i.val)
-- : (rotate_left' k P).f i = i :=
-- begin
--   induction k with k IH,
--   { refl },
--   { unfold rotate_left',
--     simp [comp_f],
--     unfold function.comp,
--     note h' := lt_of_succ_lt h,
--     rw [swap_neq,IH _ h'],
--     simp [not_or_iff_not_and_not],
--     split ; intro h' ; cases i
--     ; injection h' with h'
--     ; rw h' at h,
--     { apply nat.lt_irrefl _ h },
--     { apply nat.lt_irrefl _ (lt_of_succ_lt h) } }
-- end

-- lemma rotate_right_gt_eq_self {n : ℕ} (k : ℕ) (P : k < n) (i : fin n)
--   (h : n - succ k > i.val)
-- : (rotate_right' k P).f i = i :=
-- begin
--   induction k with k IH,
--   { refl },
--   { unfold rotate_right',
--     simp [comp_f],
--     unfold function.comp,
--     assert h' : n - succ k > i.val,
--     { rw sub_succ at h,
--       apply lt_of_pred_lt h },
--     note h'' := i.is_lt,
--     rw [swap_neq, IH _ h'],
--     simp [not_or_iff_not_and_not],
--     split
--     ; apply fin.ne_of_vne ; unfold fin.val,
--     apply ne_of_gt h',
--     apply ne_of_gt h, },
-- end

-- lemma rotate_left_lt_shifted {n : ℕ} (k : ℕ) (P : k < succ n) (i : fin (succ n))
--   (h : i.val < k)
-- : (rotate_left' k P).f i = i+1 :=
-- begin
--   induction k with k IH,
--   { cases not_lt_zero _ h },
--   { unfold rotate_left',
--     simp [comp_f],
--     unfold function.comp,
--     note h' : succ i.val ≤ succ k := h,
--     cases lt_or_eq_of_le h' with h' h',
--     { rw [swap_neq,IH _ (lt_of_succ_lt_succ h')],
--       rw [not_or_iff_not_and_not],
--       split,
--       { apply fin.ne_of_vne,
--         unfold fin.val,
--         intro h₁, rw h₁ at h',
--         apply nat.lt_irrefl _ h' },
--       { apply fin.ne_of_vne,
--         unfold fin.val,
--         intro h₁, rw h₁ at h',
--         apply nat.lt_irrefl i.val,
--         apply lt_of_succ_lt h', }, },
--     assert h₂ : ({val := k, is_lt := lt_of_succ_lt P} : fin (succ n)) = i,
--     { injection h' with h',
--       apply fin.eq_of_veq, rw [h'] },
--     assert h₃ : ({val := succ k, is_lt := P} : fin (succ n)) = i + 1,
--     { rw [-h₂],
--       apply fin.eq_of_veq,
--       rw [fin.add_def],
--       unfold fin.val one has_one.one fin.of_nat,
--       rw [-mod_add',mod_eq_of_lt,-add_one_eq_succ k],
--       { rw add_one_eq_succ k, apply P } },
--     rw [h₂,swap_left,h₃],
--     apply rotate_left_gt_eq_self,
--     rw [-h₃], unfold fin.val,
--     apply lt_succ_self }
-- end

-- lemma rotate_right_lt_shifted {n : ℕ} (k : ℕ) (P : k < succ n) (i : fin (succ n))
--   (h : i.val < n - succ k)
-- : (rotate_right' k P).f i = i+1 :=
-- begin

--   induction k with k IH,
--   { cases not_lt_zero _ h },
--   { unfold rotate_left',
--     simp [comp_f],
--     unfold function.comp,
--     note h' : succ i.val ≤ succ k := h,
--     cases lt_or_eq_of_le h' with h' h',
--     { rw [swap_neq,IH _ (lt_of_succ_lt_succ h')],
--       rw [not_or_iff_not_and_not],
--       split,
--       { apply fin.ne_of_vne,
--         unfold fin.val,
--         intro h₁, rw h₁ at h',
--         apply nat.lt_irrefl _ h' },
--       { apply fin.ne_of_vne,
--         unfold fin.val,
--         intro h₁, rw h₁ at h',
--         apply nat.lt_irrefl i.val,
--         apply lt_of_succ_lt h', }, },
--     assert h₂ : ({val := k, is_lt := lt_of_succ_lt P} : fin (succ n)) = i,
--     { injection h' with h',
--       apply fin.eq_of_veq, rw [h'] },
--     assert h₃ : ({val := succ k, is_lt := P} : fin (succ n)) = i + 1,
--     { rw [-h₂],
--       apply fin.eq_of_veq,
--       rw [fin.add_def],
--       unfold fin.val one has_one.one fin.of_nat,
--       rw [-mod_add',mod_eq_of_lt,-add_one_eq_succ k],
--       { rw add_one_eq_succ k, apply P } },
--     rw [h₂,swap_left,h₃],
--     apply rotate_left_gt_eq_self,
--     rw [-h₃], unfold fin.val,
--     apply lt_succ_self }
-- end

-- lemma rotate_left_eq {n : ℕ} (k : fin (succ n)) (P : k.val < succ n)
-- : (rotate_left' k.val P).f k = 0  :=
-- begin
--   cases k with k P',
--   unfold fin.val, unfold fin.val at P,
--   induction k with k IH,
--   { unfold rotate_left',
--     unfold zero has_zero.zero fin.of_nat,
--     apply fin.eq_of_veq,
--     unfold fin.val,
--     rw [mod_eq_of_lt P],
--     refl, },
--   { unfold rotate_left',
--     simp [comp_f], unfold function.comp,
--     simp [swap_right],
--     apply IH, }
-- end

-- lemma rotate_right_eq {n : ℕ} (k : fin (succ n)) (P : k.val < succ n)
-- : (rotate_right' k.val P).f k = fin.max :=
-- begin
--   cases k with k P',
--   unfold fin.val, unfold fin.val at P,
--   induction k with k IH,
--   { unfold rotate_right',
--     unfold zero has_zero.zero fin.of_nat,
--     apply fin.eq_of_veq,
--     unfold fin.val,
--     rw [mod_eq_of_lt P],
--     refl, },
--   { unfold rotate_left',
--     simp [comp_f], unfold function.comp,
--     simp [swap_right],
--     apply IH, }
-- end

-- def rotate_left : ∀ n, perm n
--   | 0 := id
--   | (succ n) := rotate_left' n (lt_succ_self _)

def rotate_right_f : ∀ {n} (k i : fin n), fin n
  | 0 k i := i
  | (succ n) k i := if k.val = i.val then ⟨n,lt_succ_self _⟩
                    else if k.val < i.val then i.pred'
                    else i

def rotate_right_g : ∀ {n} (k i : fin n), fin n
  | 0 k i := i
  | (succ n) k i := if i.val = n then k
                    else if k.val ≤ i.val then i.succ
                    else i

-- def rotate_right_inverse (k x y : fin n)
-- : rotate_right_f k x = y ↔ x = rotate_right_g k y :=
-- begin
--   cases n with n ;
--   unfold rotate_right_f,
--   { unfold rotate_right_g, refl },
--   { cases decidable.em (k = x) with h h,
--     { rw [if_pos h,eq_comm],
--       unfold rotate_right_g,
--       split ; intro h₁,
--       { rw [if_pos h₁,h], },
--       { apply classical.by_contradiction,
--         intro h₂,
--         rw [if_neg h₂] at h₁,
--         subst x,
--         cases le_or_gt k y with h₃ h₃,
--         { rw [if_pos] at h₁,
--           subst k, apply fin.succ_le_self _ _ h₃, }, },  }, }
-- end

open fin

-- set_option pp.notation false
-- set_option pp.implicit true

-- #check has_neg (fin n)

def rotate_right (k : fin n) : perm n :=
bijection.mk (rotate_right_f k) (rotate_right_g k)
begin
  intro x,
  cases n with n, refl,
  { unfold rotate_right_f,
    cases decidable.em (k.val = x.val) with Heq Heq,
    { rw [if_pos Heq],
      unfold rotate_right_g,
      rw [if_pos,eq_of_veq Heq],
      refl },
    { rw [if_neg Heq],
      cases lt_or_gt_of_ne Heq with Hlt Hgt,
      { rw [if_pos Hlt],
        unfold rotate_right_g,
        note Hx_pos' : 0 < x.val :=
           lt_of_le_of_lt (zero_le _) Hlt,
        assert Hx_pos : 0 < x,
        { rw [lt_def,zero_def],
          apply Hx_pos' },
        rw [if_neg,if_pos],
        { apply fin.succ_pred _ Hx_pos },
        { apply le_of_succ_le_succ,
          apply nat.le_trans Hlt,
          apply nat.le_trans _ (fin.val_succ_le_nat_succ _),
          rw [fin.succ_pred _ Hx_pos], },
        { apply ne_of_lt, rw pred_def,
          apply lt_of_succ_lt_succ,
          rw [succ_pred_eq_of_pos Hx_pos'],
          apply x.is_lt, }, },
      { note Hn_lt := not_lt_of_gt Hgt,
        note Hn_le := not_le_of_gt Hgt,
        rw [if_neg Hn_lt],
        unfold rotate_right_g,
        rw [if_neg Hn_le,if_neg],
        apply ne_of_lt,
        apply lt_of_lt_of_le Hgt,
        apply le_of_succ_le_succ k.is_lt }, }, },
end
begin
  intro x,
  cases n with n, refl,
  { unfold rotate_right_g,
    cases decidable.em (x.val = n) with Heq_n Hne_n,
    { rw if_pos Heq_n,
      unfold rotate_right_f,
      rw if_pos rfl,
      apply eq_of_veq,
      rw Heq_n },
    { rw if_neg Hne_n,
      cases decidable.em (k.val ≤ x.val) with Hle Hn_le,
      { rw if_pos Hle,
        unfold rotate_right_f,
        assert Hne : k.val ≠ (succ x).val,
        { apply ne_of_lt, rw [fin.succ_def],
          { apply succ_le_succ Hle },
          { apply lt_of_le_of_ne,
            apply x.is_lt,
            intro h, apply Hne_n,
            injection h with h, apply h } },
        rw [if_neg Hne,if_pos,fin.pred_succ],
        { apply succ_lt_succ,
          apply lt_of_le_of_ne _ Hne_n,
          apply le_of_succ_le_succ,
          apply x.is_lt },
        { apply lt_of_le_of_ne _ Hne,
          apply le_trans Hle,
          rw [-le_def],
          apply fin.le_succ_self, }, },
      { assert Hne : k.val ≠ x.val,
        { apply ne_of_gt,
          apply lt_of_not_le Hn_le },
        rw if_neg Hn_le,
        unfold rotate_right_f,
        rw [if_neg Hne,if_neg],
        apply not_lt_of_ge,
        apply le_of_not_le Hn_le, }, }, },
end

-- lemma taken_length (xs : list α)
-- : taken (length xs) xs = xs :=
-- begin
--   induction xs with x xs IH,
--   { refl },
--   { simp [IH] }
-- end

-- lemma dropn_length (xs : list α)
-- : dropn (length xs) xs = [] :=
-- begin
--   induction xs with x xs IH,
--   { refl },
--   { simp [IH] }
-- end

-- lemma length_to_list {n : ℕ} (x : perm n) : length x.to_list = n :=
-- bijection.length_to_list x

-- lemma rotate_left_swaps
--   {x : fin n} {xs : list (fin n)}
--   (h : (rotate_left n).to_list = x :: xs)
-- : (rotate_left n).to_list = xs ++ [x] :=
-- begin
--   cases n with n,
--   { note Hlength := length_to_list (rotate_left 0),
--     rw h at Hlength,
--     simp [add_one_eq_succ] at Hlength,
--     contradiction, },
--   note h' := rotate_left'.f_swaps _ h,
--   note Htaken := taken_length xs,
--   note Hdropn := dropn_length xs,
--   assert Hlength : length xs = n,
--   { note Hlength := length_to_list (rotate_left (succ n)),
--     rw h at Hlength,
--     simp [add_one_eq_succ] at Hlength,
--     injection Hlength with H, apply H },
--   rw Hlength at Htaken Hdropn,
--   simp [Htaken,Hdropn] at h',
--   apply h',
-- end

@[simp]
lemma rotate_right_f_eq {n : ℕ} (k : fin n)
: (rotate_right k).f = rotate_right_f k :=
by refl

@[simp]
lemma rotate_right_g_eq {n : ℕ} (k : fin n)
: (rotate_right k).g = rotate_right_g k :=
by refl

lemma rotate_right_f_k {n : ℕ} (k : fin (succ n))
: (rotate_right k).f k = fin.max :=
begin
  simp,
  unfold rotate_right_f,
  rw [if_pos rfl],
  refl
end

lemma rotate_right_g_max {n : ℕ} (k : fin (succ n))
: (rotate_right k).g fin.max = k :=
begin
  symmetry,
  rw [-bijection.inverse,rotate_right_f_k],
end

lemma rotate_right_f_lt_shifted {n : ℕ} (k i : fin n)
  (h : k < i)
: (rotate_right k).f i = i.pred' :=
begin
  cases n with n
  ; simp
  ; unfold rotate_right_f,
  { cases i with i Hi, unfold fin.succ,
    cases not_lt_zero _ Hi },
  { rw [if_neg,if_pos],
    rw -lt_def, apply h,
    apply ne_of_lt,
    rw [-lt_def], apply h }
end

lemma rotate_right_g_lt_shifted {n : ℕ} (k i : fin n)
  (h : k < i)
: (rotate_right k).g i.pred' = i :=
begin
  symmetry,
  rw [-bijection.inverse,rotate_right_f_lt_shifted _ _ h],
end

lemma rotate_right_f_gt_eq_self {n : ℕ} (k i : fin n)
  (h : k > i)
: (rotate_right k).f i = i :=
begin
  cases n with n
  ; simp
  ; unfold rotate_right_f, refl,
  rw [if_neg,if_neg],
  { apply not_lt_of_gt,
    unfold gt,
    rw [-lt_def],
    apply h },
  { apply ne_of_gt,
    unfold gt,
    rw [-lt_def],
    apply h }
end

lemma rotate_right_g_gt_eq_self {n : ℕ} (k i : fin n)
  (h : k > i)
: (rotate_right k).g i = i :=
begin
  symmetry,
  rw -bijection.inverse,
  apply rotate_right_f_gt_eq_self _ _ h,
end

end perm
