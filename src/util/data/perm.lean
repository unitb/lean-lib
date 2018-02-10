
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
  ; simp [swap_inverse']
  ; refl
end

lemma swap_symmetry [decidable_eq α] (i j : α)
: swap i j = swap j i :=
begin
  apply bijection.eq
  ; intro x
  ; simp [comp_f,comp_g]
  ; simp [swap_symmetry']
end

end bijection

def perm (n : ℕ) := bijection (fin n) (fin n)

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

def rotate_right_f : ∀ {n} (k i : fin n), fin n
  | 0 k i := i
  | (succ n) k i := if k.val = i.val then ⟨n,lt_succ_self _⟩
                    else if k.val < i.val then i.pred'
                    else i

def rotate_right_g : ∀ {n} (k i : fin n), fin n
  | 0 k i := i
  | (succ n) k i := if i.val = n then k
                    else if k.val ≤ i.val then i.succ'
                    else i

open fin

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
        have Hx_pos' : 0 < x.val :=
           lt_of_le_of_lt (zero_le _) Hlt,
        have Hx_pos : 0 < x,
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
      { have Hn_lt := not_lt_of_gt Hgt,
        have Hn_le := not_le_of_gt Hgt,
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
        have Hne : k.val ≠ (succ' x).val,
        { apply ne_of_lt, rw [fin.succ_def],
          { apply succ_le_succ Hle },
          { apply lt_of_le_of_ne,
            apply x.is_lt,
            intro h, apply Hne_n,
            injection h with h, } },
        rw [if_neg Hne,if_pos,fin.pred_succ],
        { apply succ_lt_succ,
          apply lt_of_le_of_ne _ Hne_n,
          apply le_of_succ_le_succ,
          apply x.is_lt },
        { apply lt_of_le_of_ne _ Hne,
          apply le_trans Hle,
          rw [← le_def],
          apply fin.le_succ_self, }, },
      { have Hne : k.val ≠ x.val,
        { apply ne_of_gt,
          apply lt_of_not_le Hn_le },
        rw if_neg Hn_le,
        unfold rotate_right_f,
        rw [if_neg Hne,if_neg],
        apply not_lt_of_ge,
        apply le_of_not_le Hn_le, }, }, },
end

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
  rw [← bijection.inverse,rotate_right_f_k],
end

lemma rotate_right_f_lt_shifted {n : ℕ} (k i : fin n)
  (h : k < i)
: (rotate_right k).f i = i.pred' :=
begin
  cases n with n
  ; simp
  ; unfold rotate_right_f,
  { cases i with i Hi,
    cases not_lt_zero _ Hi },
  { rw [if_neg,if_pos],
    rw ← lt_def, apply h,
    apply ne_of_lt,
    rw [← lt_def], apply h }
end

lemma rotate_right_g_lt_shifted {n : ℕ} (k i : fin n)
  (h : k < i)
: (rotate_right k).g i.pred' = i :=
begin
  symmetry,
  rw [← bijection.inverse,rotate_right_f_lt_shifted _ _ h],
end

lemma rotate_right_f_gt_eq_self {n : ℕ} (k i : fin n)
  (h : k > i)
: (rotate_right k).f i = i :=
begin
  cases n with n
  ; simp
  ; unfold rotate_right_f,
  rw [if_neg,if_neg],
  { apply not_lt_of_gt,
    unfold gt,
    rw [← lt_def],
    apply h },
  { apply ne_of_gt,
    unfold gt,
    rw [← lt_def],
    apply h }
end

lemma rotate_right_g_gt_eq_self {n : ℕ} (k i : fin n)
  (h : k > i)
: (rotate_right k).g i = i :=
begin
  symmetry,
  rw ← bijection.inverse,
  apply rotate_right_f_gt_eq_self _ _ h,
end

def rotate_right' {n : ℕ} (i : fin n) : perm n :=
rev (rotate_right i)

def to_total_aux {n : ℕ} (f : fin n → fin n) (i : ℕ) : ℕ :=
if h : i < n then (f ⟨i,h⟩).val else i

lemma to_total_f_inverse (p : perm n) (x : ℕ)
: to_total_aux (p.g) (to_total_aux (p.f) x) = x :=
begin
  cases decidable.em (x < n) with h h,
  { unfold to_total_aux,
    rw [dif_pos h,dif_pos (p.f ⟨x, h⟩).is_lt],
    have h : (⟨(p.f ⟨x, h⟩).val, (p.f ⟨x, h⟩).is_lt⟩ : fin n) = p.f ⟨x, h⟩,
    { apply eq_of_veq, refl },
    rw [h,p.f_inv], },
  { unfold to_total_aux,
    rw [dif_neg h,dif_neg h], }
end

lemma to_total_g_inverse (p : perm n) (x : ℕ)
: to_total_aux (p.f) (to_total_aux (p.g) x) = x :=
begin
  have h := to_total_f_inverse (rev p) x,
  rw [rev_f,rev_g] at h,
  apply h
end

def to_total {n : ℕ} (p : perm n) : bijection ℕ ℕ :=
bijection.mk
  (to_total_aux p.f)
  (to_total_aux p.g)
  (to_total_f_inverse p)
  (to_total_g_inverse p)

lemma to_total_g_eq_self_of_ge {n : ℕ} (p : perm n) {x : ℕ}
  (h : n ≤ x)
: (to_total p).g x = x :=
begin
  unfold to_total bijection.mk bijection.g to_total_aux,
  rw dif_neg (not_lt_of_ge h),
end

lemma to_total_g_eq_of_lt {n : ℕ} (p : perm n) {x : ℕ}
  (h : x < n)
: (to_total p).g x = (p.g ⟨x,h⟩).val :=
begin
  unfold to_total bijection.mk bijection.g to_total_aux,
  rw dif_pos h,
end

end perm

namespace bijection

def rotate_right (i j : ℕ) (h : i < j) : bijection ℕ ℕ :=
@perm.to_total j (perm.rotate_right ⟨i,h⟩)

def rotate_right' (i j : ℕ) (h : i < j) : bijection ℕ ℕ :=
@perm.to_total j (perm.rotate_right' ⟨i,h⟩)

lemma rotate_right'_g_eq_of_ge_j {i j : ℕ} (x : ℕ)
  (Hij : i < j)
  (Hjx : j ≤ x)
: (rotate_right' i j Hij).g x = x :=
begin
  unfold rotate_right',
  apply perm.to_total_g_eq_self_of_ge _ Hjx,
end

lemma rotate_right'_g_eq_of_lt_i {i j : ℕ} (x : ℕ)
  (Hij : i < j)
  (Hxi : x < i)
: (rotate_right' i j Hij).g x = x :=
begin
  unfold rotate_right' perm.rotate_right',
  rw [perm.to_total_g_eq_of_lt _ (lt_trans Hxi Hij),rev_g
     ,perm.rotate_right_f_gt_eq_self],
  apply Hxi,
end

lemma succ_rotate_right'_g_eq_self {i j : ℕ} (x : ℕ)
  (Hij : i < j)
  (Hix : i < x)
  (Hxj : x < j)
: nat.succ ((rotate_right' i j Hij).g x) = x :=
begin
  unfold rotate_right' perm.rotate_right',
  rw [perm.to_total_g_eq_of_lt _ Hxj,rev_g
     ,perm.rotate_right_f_lt_shifted
     ,fin.pred_def,nat.succ_pred_eq_of_pos],
  { unfold fin.val,
    apply lt_of_le_of_lt _ Hix,
    apply nat.zero_le },
  { apply Hix },
end

end bijection
