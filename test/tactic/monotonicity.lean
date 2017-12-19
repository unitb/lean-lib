
import util.meta.tactic

open list tactic tactic.interactive

meta class elaborable (α : Type) (β : inout Type) :=
  (elaborate : α → tactic β)

export elaborable (elaborate)

meta instance : elaborable pexpr expr :=
⟨ to_expr ⟩

meta instance elaborable_list {α α'} [elaborable α α'] : elaborable (list α) (list α') :=
⟨ mmap (elaborate _) ⟩

meta def mono_function.elaborate : mono_function ff → tactic mono_function
| (mono_function.non_assoc x y z) :=
mono_function.non_assoc <$> elaborate _ x
                        <*> elaborate _ y
                        <*> elaborate _ z
| (mono_function.assoc x y z) :=
mono_function.assoc <$> elaborate _ x
                    <*> traverse (elaborate _) y
                    <*> traverse (elaborate _) z
| (mono_function.assoc_comm x y) :=
mono_function.assoc_comm <$> elaborate _ x
                         <*> elaborate _ y


meta instance elaborable_mono_function : elaborable (mono_function ff) mono_function :=
⟨ mono_function.elaborate ⟩

meta instance prod_elaborable {α α' β β' : Type} [elaborable α α']  [elaborable β β']
: elaborable (α × β) (α' × β') :=
⟨ λ i, prod.rec_on i (λ x y, prod.mk <$> elaborate _ x <*> elaborate _ y) ⟩

meta def parse_mono_function' (l r : pexpr) :=
do l' ← to_expr l,
   r' ← to_expr r,
   parse_mono_function { monotonicity_cfg . } l' r'

run_cmd
do xs ← mmap to_expr [``(1),``(2),``(3)],
   ys ← mmap to_expr [``(1),``(2),``(4)],
   x ← match_prefix { unify := ff } xs ys,
   p ← elaborate _ ([``(1),``(2)] , [``(3)], [``(4)]),
   guard $ x = p

run_cmd
do xs ← mmap to_expr [``(1),``(2),``(3),``(6),``(7)],
   ys ← mmap to_expr [``(1),``(2),``(4),``(5),``(6),``(7)],
   x ← match_assoc { unify := ff } xs ys,
   p ← elaborate _ ([``(1), ``(2)], [``(3)], ([``(4), ``(5)], [``(6), ``(7)])),
   guard (x = p)

run_cmd
do x ← to_expr ``(7 + 3 : ℕ) >>= check_ac,
   x ← pp x.2.2.1,
   guard $ x.to_string = "(some (is_left_id.left_id has_add.add 0, (is_right_id.right_id has_add.add 0, 0)))"

run_cmd
do parse_mono_function' ``(1 + 3 + 2 + 6) ``(4 + 2 + 1 + 5) >>= tactic.trace,
   parse_mono_function' ``([1] ++ [3] ++ [2] ++ [6]) ``([4] ++ [2] ++ ([1] ++ [5]))
     >>= tactic.trace,
   parse_mono_function' ``([1] ++ [3] ++ [2] ++ [2]) ``([1] ++ [5] ++ ([4] ++ [2]))
     >>= tactic.trace

lemma bar
  (h : 3 + 6 ≤ 4 + 5)
: 1 + 3 + 2 + 6 ≤ 4 + 2 + 1 + 5 :=
begin
  monotonicity1,
  apply h
end

lemma bar'
  (h : 3 ≤ (4 : ℤ))
  (h' : 5 ≤ (6 : ℤ))
: (1 + 3 + 2) - 6 ≤ (4 + 2 + 1 : ℤ) - 5 :=
begin
  transitivity (1 + 3 + 2 - 5 : ℤ),
  monotonicity1,
  apply h',
  monotonicity1,
  monotonicity1,
  apply h
end

@[simp]
def list.le' {α : Type*} [has_le α] : list α → list α → Prop
 | (x::xs) (y::ys) := x ≤ y ∧ list.le' xs ys
 | [] [] := true
 | _ _ := false

@[simp]
instance list_has_le {α : Type*} [has_le α] : has_le (list α) :=
⟨ list.le' ⟩

@[refl]
lemma list.le_refl {α : Type*} [preorder α] {xs : list α}
: xs ≤ xs :=
begin
  induction xs with x xs,
  { trivial },
  { simp [has_le.le,list.le],
    split, apply le_refl, apply ih_1 }
end

-- @[trans]
lemma list.le_trans {α : Type*} [preorder α]
  {xs zs : list α} (ys : list α)
  (h  : xs ≤ ys)
  (h' : ys ≤ zs)
: xs ≤ zs :=
begin
  revert ys zs,
  induction xs with x xs
  ; intros ys zs h h'
  ; cases ys with y ys
  ; cases zs with z zs
  ; try { cases h ; cases h' ; done },
  { refl },
  { simp [has_le.le,list.le],
    split,
    apply le_trans h.left h'.left,
    apply ih_1 _ h.right h'.right, }
end

@[monotonic]
lemma list_le_mono_left {α : Type*} [preorder α] {xs ys zs : list α}
  (h : xs ≤ ys)
: xs ++ zs ≤ ys ++ zs :=
begin
  revert ys,
  induction xs with x xs ; intros ys h,
  { cases ys, refl, cases h },
  { cases ys with y ys, cases h, simp [has_le.le,list.le] at *,
    revert h, apply and.imp_right,
    apply ih_1 }
end

@[monotonic]
lemma list_le_mono_right {α : Type*} [preorder α] {xs ys zs : list α}
  (h : xs ≤ ys)
: zs ++ xs ≤ zs ++ ys :=
begin
  revert ys zs,
  induction xs with x xs ; intros ys zs h,
  { cases ys, { simp }, cases h  },
  { cases ys with y ys, cases h, simp [has_le.le,list.le] at *,
    rw [list.append_cons _ x,list.append_cons _ y],
    apply list.le_trans (zs ++ [y] ++ xs),
    { apply list_le_mono_left,
      induction zs with z zs,
      { simp [has_le.le,list.le], apply h.left },
      { simp [has_le.le,list.le], split, apply le_refl,
        apply ih_1_1, } },
    { apply ih_1 h.right, } }
end

lemma bar_bar'
  (h : [] ++ [3] ++ [2] ≤ [1] ++ [5] ++ [4])
: [] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
begin
  monotonicity1,
  apply h
end

lemma bar_bar''
  (h : [3] ++ [2] ++ [2] ≤ [5] ++ [4] ++ [])
: [1] ++ ([3] ++ [2]) ++ [2] ≤ [1] ++ [5] ++ ([4] ++ []) :=
begin
  monotonicity1,
  apply h,
end

lemma bar_bar
  (h : [3] ++ [2] ≤ [5] ++ [4])
: [1] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
begin
  monotonicity1,
  apply h
end

def P (x : ℕ) := 7 ≤ x
def Q (x : ℕ) := x ≤ 7

@[monotonic]
lemma P_mono {x y : ℕ}
  (h : x ≤ y)
: P x → P y :=
by { intro h', apply le_trans h' h }

@[monotonic]
lemma Q_mono {x y : ℕ}
  (h : y ≤ x)
: Q x → Q y :=
by apply le_trans h

example (x y z : ℕ)
  (h : x ≤ y)
: P (x + z) → P (z + y) :=
begin
  monotonicity1,
  monotonicity1,
  apply h,
end

example (x y z : ℕ)
  (h : y ≤ x)
: Q (x + z) → Q (z + y) :=
begin
  monotonicity1,
  monotonicity1,
  apply h,
end

example {α β : Type} (p q : α → β → Prop) (r : α → Prop) (s : β → Prop)
  (h : ∀ x y, r x → ¬ s y → q x y → p x y)
: (∃ x, ∀ y, r x ∧ (¬ p x y ∨ s y))
→ (∃ i, ∀ j, r i ∧ (¬ q i j ∨ s j)) :=
begin
  intro_mono k,
  intro_mono z,
  intro_mono i,
  intro_mono j,
  intro_mono ,
  apply h ; assumption
end

example {α β : Type} (p q : α → β → Prop) (r : α → Prop) (s : β → Prop)
  (h : ∀ x y, r x → ¬ s y → q x y → p x y)
: (∃ x, ∀ y, r x ∧ (¬ p x y ∨ s y))
→ (∃ i, ∀ j, r i ∧ (¬ q i j ∨ s j)) :=
begin
  intros_mono,
  apply h ; assumption
end

example {α β : Type} (p q : α → β → Prop) (r : α → Prop) (s : β → Prop)
  (h : ∀ x y, r x → ¬ s y → q x y → p x y)
: (∃ x, ∀ y, r x ∧ (¬ p x y ∨ s y))
→ (∃ i, ∀ j, r i ∧ (¬ q i j ∨ s j)) :=
begin
  intros_mono,
  apply h ; assumption,
end

example {α β : Type} (p : α → β → Prop) (q r : α → Prop) (s : β → Prop)
  (h : ∀ x y, r x → ¬ q x → p x y → r x)
: (∃ x, ∀ y : β, r x ∧ (¬ r x ∨ q x))
→ (∃ i, ∀ j, r i ∧ (¬ p i j ∨ q i)) :=
begin
  introv_mono h₀ h₁,
  apply h ; assumption,
end

example {α β : Type} (p q : α → β → ℕ) (r : α → Prop) (s : β → Prop)
  (h : ∀ x y, r x → ¬ s y → p x y ≤ q x y)
: (∃ x, ∀ y, r x ∧ (P (p x y) ∨ s y))
→ (∃ i, ∀ j, r i ∧ (P (q i j) ∨ s j)) :=
begin
  introv_mono h₀ h₁,
  auto,
end

example (x y z k m n : ℤ)
  (h₀ : z ≤ 0)
  (h₁ : y ≤ x)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  monotonicity1,
  monotonicity1,
  monotonicity1,
  auto
end

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  monotonicity1,
  monotonicity1,
  monotonicity1,
  auto
end

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by  monotonicity h₁

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : m + x + n ≤ y + n + m)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by monotonicity h₁

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : n + x + m ≤ y + n + m)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  monotonicity : m + x + n ≤ y + n + m,
  transitivity ; [ skip , apply h₁ ],
  apply le_of_eq,
  ac_refl,
end

example (x y z k m n : ℕ)
  (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  monotonicity1,
  success_if_fail { monotonicity1 }, -- can't prove 0 ≤ z
  admit,
end

example (x y z k m n : ℕ)
  (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  monotonicity,
  change (m + x + n) * z ≤ z * (y + n + m),
  admit,
end

example (x y z k m n i j : ℕ)
  (h₁ : x + i = y + j)
: (m + x + n + i) * z + k = z * (j + n + m + y) + k :=
begin
  monotonicity1,
  monotonicity1,
  monotonicity1,
  simp [h₁],
end

example (x y z k m n i j : ℕ)
  (h₁ : x + i = y + j)
: (m + x + n + i) * z + k = z * (j + n + m + y) + k :=
begin
  monotonicity,
  simp [h₁],
end

example (x y : ℕ)
  (h : x ≤ y)
: true :=
begin
  (do v ← mk_mvar,
      p ← to_expr ```(%%v + x ≤ y + %%v),
      assert `h' p),
  monotonicity h,
  trivial,
  exact 1,
end
