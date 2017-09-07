
import util.data.array
import util.data.nat
import util.data.sigma

import data.prod

universe variables u₀ u₁ u₂ u₃ u₄

section bijection

variables {α α' : Type (u₀)}
variables {β β' : Type (u₁)}
variables {γ : Type u₂}

structure bijection (α  : Type (u₀)) (β : Type (u₁)) : Type (max (u₀) (u₁)) :=
  mk' ::
  (f : α → β)
  (g : β → α)
  (inverse : ∀ x y, f x = y ↔ x = g y)

def bijection.mk (f : α → β) (g : β → α)
    (f_inv : ∀ x, g (f x) = x)
    (g_inv : ∀ x, f (g x) = x) : bijection α β :=
  { f := f, g := g, inverse :=
    begin
      intros x y,
      split ; intro h,
      { subst y, rw f_inv },
      { subst x, rw g_inv },
    end }

lemma bijection.f_inv (b : bijection α β) (x : α) : b^.g (b^.f x) = x := begin
  symmetry,
  rw [← b^.inverse]
end

lemma bijection.g_inv (b : bijection α β) (x : β) : b^.f (b^.g x) = x := begin
  rw [b^.inverse]
end

lemma bijection.f_inv' (b : bijection α β) : b^.g ∘ b^.f = id :=
begin
  apply funext,
  unfold function.comp,
  apply bijection.f_inv
end

lemma bijection.g_inv' (b : bijection α β) : b^.f ∘ b^.g = id :=
begin
  apply funext,
  unfold function.comp,
  apply bijection.g_inv
end

lemma bijection.f_injective (b : bijection α β)
: function.injective (b.f) :=
begin
  intros i j,
  rw [b.inverse,b.f_inv],
  apply id
end

lemma bijection.g_injective (b : bijection α β)
: function.injective (b.g) :=
begin
  intros i j,
  rw [← b.inverse,b.g_inv],
  apply id
end

def bijection.id : bijection α α :=
    bijection.mk id id (λ _, by simp) (λ _, by simp)

class finite (α : Type (u₀)) : Type (u₀) :=
  (count : ℕ)
  (to_nat : bijection α (fin count))

class pos_finite (α : Type (u₀)) : Type (u₀) :=
  (pred_count : ℕ)
  (to_nat : bijection α (fin $ nat.succ pred_count))

class infinite (α : Type u₀) : Type u₀ :=
  (to_nat : bijection α ℕ)

instance inhabited_of_pos_finite [pos_finite α] : inhabited α :=
{ default := ((pos_finite.to_nat α).g fin.max) }

def pos_of_finite {α} [finite α] [_ne : nonempty α] : pos_finite α :=
  { pred_count := nat.pred (finite.count α)
  , to_nat :=
    begin
      rw nat.succ_pred_eq_of_pos,
      apply finite.to_nat,
      cases _ne with x,
      have H := ((finite.to_nat α).f x).is_lt,
      apply lt_of_le_of_lt (nat.zero_le _) H,
    end }

instance finite_of_pos_finite [pos_finite α] : finite α :=
{ count := nat.succ (pos_finite.pred_count α)
, to_nat := pos_finite.to_nat α }

def bij.comp (x : bijection β γ) (y : bijection α β) : bijection α γ :=
   { f := x^.f ∘ y^.f
   , g := y^.g ∘ x^.g
   , inverse :=
       begin
         intros a b,
         unfold function.comp,
         rw [x^.inverse,y^.inverse]
       end }

lemma comp_f  (x : bijection β γ) (y : bijection α β)
: (bij.comp x y).f = x.f ∘ y.f := rfl

lemma comp_g  (x : bijection β γ) (y : bijection α β)
: (bij.comp x y).g = y.g ∘ x.g := rfl

def sum.swap : α ⊕ β → β ⊕ α
  | (sum.inl x) := sum.inr x
  | (sum.inr x) := sum.inl x

def bij.sum.swap : bijection (α ⊕ β) (β ⊕ α) :=
   bijection.mk sum.swap sum.swap
   (by intro x ; cases x with x x ; unfold sum.swap ; refl)
   (by intro x ; cases x with x x ; unfold sum.swap ; refl)

def bij.prod.swap : bijection (α × β) (β × α) :=
   bijection.mk prod.swap prod.swap
   (by intro x ; cases x with x x ; refl)
   (by intro x ; cases x with x x ; refl)

def bijection.rev (x : bijection α β) : bijection β α :=
  { f := x^.g
  , g := x^.f
  , inverse :=
    begin
      intros i j,
      split ; intro h ; symmetry,
      { rw [x^.inverse,h] },
      { rw [← x^.inverse,← h], }
    end }

open bijection

@[simp]
lemma rev_f  (x : bijection α β)
: (rev x).f = x.g := rfl

@[simp]
lemma rev_g  (x : bijection α β)
: (rev x).g = x.f := rfl

end bijection

namespace bijection

protected lemma eq {α β} (b₀ b₁ : bijection α β)
  (Hf : ∀ x, b₀.f x = b₁.f x)
  (Hg : ∀ x, b₀.g x = b₁.g x)
: b₀ = b₁ :=
begin
  cases b₀, cases b₁,
  unfold bijection.f bijection.g at Hf Hg,
  have Hf' : f = f_1 := funext Hf,
  have Hg' : g = g_1 := funext Hg,
  subst f_1, subst g_1
end

infixr ∘ := bij.comp

lemma bijection.left_id {α β} (x : bijection α β) : id ∘ x = x :=
begin
  cases x, unfold id bij.comp,
  have Hf : function.comp id.f f = f := function.left_id _,
  have Hg : function.comp g id.g = g := function.right_id _,
  simp [Hf,Hg],
  refl
end

lemma bijection.right_id {α β} (x : bijection α β) : x ∘ id = x :=
begin
  cases x, unfold id bij.comp,
  have Hf : function.comp f id.f = f := function.left_id _,
  have Hg : function.comp id.g g = g := function.left_id _,
  simp [Hf,Hg],
  refl,
end

@[simp]
lemma bijection.comp_assoc {α β γ φ} (z : bijection α β) (y : bijection β γ) (x : bijection γ φ)
: (x ∘ y) ∘ z = x ∘ (y ∘ z) :=
begin
  cases x with Xf Xg Xinv,
  cases y with Yf Yg Yinv,
  cases z with Zf Zg Zinv,
  unfold bij.comp bijection.f bijection.g,
end

section pre

parameter (n : ℕ)

def bij.sum.pre.f : fin n ⊕ ℕ → ℕ
  | (sum.inl ⟨x,Px⟩) := x
  | (sum.inr x) := x + n
def bij.sum.pre.g (i : ℕ) : fin n ⊕ ℕ :=
  if P : i < n
     then sum.inl ⟨i, P⟩
     else sum.inr (i - n)

def bij.sum.pre : bijection (fin n ⊕ ℕ) ℕ :=
  bijection.mk bij.sum.pre.f bij.sum.pre.g
  begin
    intro x
    ; cases x with x x,
    { cases x with x Px,
      unfold bij.sum.pre.f bij.sum.pre.g,
      rw [dif_pos Px] },
    { have h : ¬ x + n < n,
      { apply not_lt_of_ge, apply nat.le_add_left },
      unfold bij.sum.pre.f bij.sum.pre.g,
      rw [dif_neg h,nat.add_sub_cancel] }
  end
  begin
    intro x,
    cases decidable.em (x < n) with h h,
    { unfold bij.sum.pre.g,
      rw [dif_pos h],
      unfold bij.sum.pre.f,  },
    { unfold bij.sum.pre.g,
      rw [dif_neg h],
      unfold bij.sum.pre.f,
      rw [nat.sub_add_cancel],
      apply le_of_not_gt h }
  end

open nat

def bij.prod.pre.f : fin n × ℕ → ℕ
  | (⟨x,Px⟩,y) := x + y * n
def bij.prod.pre.g (i : ℕ) : fin (succ n) × ℕ :=
  (⟨i % succ n, nat.mod_lt _ $ zero_lt_succ _⟩, i / succ n)

end pre
def bij.prod.pre (n) : bijection (fin (nat.succ n) × ℕ) ℕ :=
  bijection.mk (bij.prod.pre.f _) (bij.prod.pre.g _)
begin
  intros x,
  cases x with x₀ x₁,
  cases x₀ with x₀ Px,
  unfold bij.prod.pre.g bij.prod.pre.f,
  apply congr,
  { apply congr_arg,
    apply fin.eq_of_veq, unfold fin.val,
    rw [nat.add_mul_mod_self_right _ _ _,nat.mod_eq_of_lt Px], },
  { rw [nat.add_mul_div_self_right _ Px] },
end
begin
  intros x,
  unfold bij.prod.pre.g bij.prod.pre.f,
  simp [nat.mod_add_div]
end

section append

open nat

parameters (m n : ℕ)

def bij.sum.append.f : fin m ⊕ fin n → fin (n+m)
  | (sum.inl ⟨x,Px⟩) := ⟨x,lt_of_lt_of_le Px (nat.le_add_left _ _)⟩
  | (sum.inr ⟨x,Px⟩) := ⟨x + m,add_lt_add_right Px _⟩

def bij.sum.append.g : fin (n+m) → fin m ⊕ fin n
  | ⟨x,Px⟩ :=
  if P : x < m
     then sum.inl ⟨x, P⟩
     else sum.inr ⟨x - m,
        begin
          apply @lt_of_add_lt_add_right _ _ _ m,
          rw nat.sub_add_cancel,
          apply Px, apply le_of_not_gt P
        end⟩

def bij.sum.append : bijection (fin m ⊕ fin n) (fin (n+m)) :=
  bijection.mk bij.sum.append.f bij.sum.append.g
  begin
    intro x
    ; cases x with x x,
    { cases x with x Px,
      unfold bij.sum.append.f bij.sum.append.g,
      rw [dif_pos Px] },
    { cases x with x Px,
      have h : ¬ x + m < m,
      { apply not_lt_of_ge, apply nat.le_add_left },
      unfold bij.sum.append.f bij.sum.append.g,
      rw [dif_neg h], apply congr_arg,
      apply fin.eq_of_veq, unfold fin.val,
      apply nat.add_sub_cancel }
  end
  begin
    intro x,
    cases x with x Px,
    cases decidable.em (x < m) with h h,
    { unfold bij.sum.append.g,
      rw [dif_pos h],
      unfold bij.sum.append.f, },
    { unfold bij.sum.append.g,
      rw [dif_neg h],
      unfold bij.sum.append.f,
      apply fin.eq_of_veq, unfold fin.val,
      rw [nat.sub_add_cancel],
      apply le_of_not_gt h }
  end

def bij.prod.append.f : fin m × fin n → fin (m*n)
  | (⟨x,Px⟩,⟨y,Py⟩) :=
       have h : n*x + y < m * n,
         begin
           apply lt_of_lt_of_le,
           { apply add_lt_add_left Py },
           { have h := eq.symm (nat.succ_mul x n),
             transitivity, rw [mul_comm, h],
             apply nat.mul_le_mul_right _ Px  }
         end,
    ⟨n*x + y,h⟩

def bij.prod.append.g : fin (m*n) → fin m × fin n
  | ⟨x,Px⟩ :=
         have hn : 0 < n,
           begin
             have h : 0 < m * n,
             { apply lt_of_le_of_lt _ Px,
               apply nat.zero_le },
             apply pos_of_mul_pos_left h,
             apply nat.zero_le,
           end,
         have hx : x / n < m,
           from div_lt_of_lt_mul _ Px,
         have hy : x % n < n, from nat.mod_lt _ hn,
      (⟨x / n, hx⟩, ⟨x % n, hy⟩)

def to_pair : fin m × fin n → ℕ × ℕ
  | (⟨x,_⟩, ⟨y,_⟩) := (x,y)

lemma pair.eq : ∀ (p q : fin m × fin n),
  (to_pair p = to_pair q) → p = q :=
begin
  intros p q h,
  cases p with p₀ p₁, cases q with q₀ q₁,
  cases p₀ with p₀ Hp₀, cases p₁ with p₁ Hp₁,
  cases q₀ with q₀ Hq₀, cases q₁ with q₁ Hq₁,
  unfold to_pair at h,
  injection h,
  subst q₀, subst q₁
end

lemma to_pair_prod_g (x : ℕ) (P : x < m * n)
: to_pair (bij.prod.append.g ⟨x,P⟩) = (x / n, x % n) :=
begin
  unfold bij.prod.append.g to_pair,
end

lemma val_prod_f (x₀ x₁ : ℕ) (P₀ : x₀ < m) (P₁ : x₁ < n)
: fin.val (bij.prod.append.f (⟨x₀,P₀⟩,⟨x₁,P₁⟩)) = n*x₀ + x₁ :=
begin
  unfold bij.prod.append.f fin.val,
end

def bij.prod.append : bijection (fin m × fin n) (fin (m*n)) :=
  bijection.mk bij.prod.append.f bij.prod.append.g
  begin
    intro x,
    cases x with x₀ x₁,
    cases x₀ with x₀ Px₀,
    cases x₁ with x₁ Px₁,
    apply pair.eq,
    unfold to_pair bij.prod.append.f,
    rw [to_pair_prod_g],
    rw [ nat.mul_add_mod_self_left _ _ _ Px₁
       , nat.mul_add_div_self_left _ _ _ Px₁]
  end
  begin
    intro x,
    cases x with x Px,
    apply fin.eq_of_veq,
    unfold fin.val bij.prod.append.g,
    simp [val_prod_f,mod_add_div]
  end

end append

section

open list
open nat

def less : ℕ → list ℕ
  | 0 := []
  | (succ n) := n :: less n

lemma enum_less {n k : ℕ} (h : n < k) : n ∈ less k :=
begin
  induction k with k,
  { cases nat.not_lt_zero _ h },
  { unfold less, have h' := @lt_or_eq_of_le ℕ _ _ _ h,
    cases h' with h' h',
    { apply or.inr, apply ih_1,
      apply lt_of_succ_lt_succ h' },
    { apply or.inl, injection h' with h, } }
end

end

def bij.even_odd.f (x : ℕ) : ℕ ⊕ ℕ :=
if x % 2 = 1 then sum.inr (x / 2) else sum.inl (x / 2)

def bij.even_odd.g : ℕ ⊕ ℕ → ℕ
  | (sum.inr x) := 2 * x + 1
  | (sum.inl x) := 2 * x

def bij.even_odd : bijection (ℕ ⊕ ℕ) ℕ :=
    bijection.mk bij.even_odd.g
                 bij.even_odd.f
      begin
        intro x,
        cases x with x x,
        { have h' : 2 > 0, apply nat.le_succ,
          have h : ¬ 2 * x % 2 = 1,
          { rw nat.mul_mod_right, contradiction },
          unfold bij.even_odd.g bij.even_odd.f,
          rw [if_neg h], rw [nat.mul_div_cancel_left _ h'] },
        { unfold bij.even_odd.g bij.even_odd.f,
          have h' := nat.le_refl 2,
          rw [if_pos,nat.mul_add_div_self_left _ _ _ h'],
          rw [nat.mul_add_mod_self_left _ _ _ h'] }
      end
      begin
        intros x,
        cases decidable.em (x % 2 = 1) with h h
        ; unfold bij.even_odd.f,
        { rw [if_pos h],
          unfold bij.even_odd.f bij.even_odd.g,
          have h₂ := nat.mod_add_div x 2,
          rw add_comm, rw h at h₂, apply h₂ },
        { rw [if_neg h],
          have h' : x % 2 = 0,
          { have h₂ := @nat.mod_lt x 2 (nat.le_succ _),
            have h₃ := enum_less h₂,
            unfold less has_mem.mem list.mem at h₃,
            cases h₃ with h₃ h₃,
            { cases h h₃ },
            cases h₃ with h₃ h₃,
            { apply h₃ },
            { cases h₃ } },
          { unfold bij.even_odd.g,
            have h₂ := nat.mod_add_div x 2,
            rw h' at h₂, simp at h₂, apply h₂ } },
      end

open nat

def bij.prod.succ : ℕ × ℕ → ℕ × ℕ
  | (n,0) := (0,succ n)
  | (n,succ m) := (succ n,m)

def diag : ℕ × ℕ → ℕ × ℕ → Prop :=
inv_image (prod.lex nat.lt nat.lt) (λ x, (x^.fst+x^.snd, x^.fst))

def diag_wf : well_founded diag :=
@inv_image.wf (ℕ × ℕ) _ _
        (λ x, (x^.fst+x^.snd, x^.fst))
        (prod.lex_wf nat.lt_wf nat.lt_wf)

def bij.prod.f : ℕ → ℕ × ℕ
  | 0 := (0,0)
  | (nat.succ n) := bij.prod.succ (bij.prod.f n)

def bij.prod.g : ℕ × ℕ → ℕ :=
  well_founded.fix diag_wf $
   assume ⟨x₀,x₁⟩,
   match (x₀,x₁) with
    | (0,0) := assume _, 0
    | (0,succ n) :=
       assume g : Π (y : ℕ × ℕ), diag y (0,succ n) → ℕ,
       have h : diag (n, 0) (0, succ n),
         begin
           unfold diag inv_image prod.fst prod.snd,
           apply prod.lex.left, simp, apply lt_succ_self
         end,
       succ (g (n,0) h)
    | (succ n,m) :=
       assume g : Π (y : ℕ × ℕ), diag y (succ n,m) → ℕ,
       have h : diag (n, succ m) (succ n, m),
         begin
           unfold diag inv_image prod.fst prod.snd,
           simp [add_succ,succ_add],
           apply prod.lex.right, apply lt_succ_self
         end,
       succ (g (n,succ m) h)
   end

lemma bij.prod.f_zero : bij.prod.f 0 = (0,0) := rfl

lemma bij.prod.f_succ (n : ℕ) : bij.prod.f (succ n) = bij.prod.succ (bij.prod.f n) := rfl

lemma bij.prod.g_zero_zero : bij.prod.g (0,0) = 0 :=
begin
  unfold bij.prod.g,
  rw well_founded.fix_eq,
  refl
end

lemma bij.prod.g_zero_succ (n : ℕ) : bij.prod.g (0,succ n) = succ (bij.prod.g (n,0)) :=
begin
  unfold bij.prod.g,
  rw well_founded.fix_eq,
  refl
end

lemma bij.prod.g_succ (n m : ℕ) : bij.prod.g (succ n,m) = succ (bij.prod.g (n,succ m)) :=
begin
  unfold bij.prod.g,
  rw [well_founded.fix_eq],
  unfold bij.prod.g._match_2 bij.prod.g._match_1,
end

lemma bij.prod.prod_succ_le_succ (m n : ℕ) : (bij.prod.succ (m,n))^.snd ≤ succ (n+m) :=
begin
  cases n with n ; unfold bij.prod.succ ; simp,
  rw [add_succ],
  apply le_succ_of_le,
  apply le_succ_of_le,
  apply le_add_left,
end

lemma bij.prod.g_prod_succ_eq_prod_succ_g (x : ℕ × ℕ) : bij.prod.g (bij.prod.succ x) = succ (bij.prod.g x) :=
begin
  apply well_founded.induction diag_wf x,
  clear x,
  intros x IH,
  cases x with x₀ x₁,
  cases x₀ with x₀,
  { cases x₁ with x₁,
    { unfold bij.prod.succ,
      rw [bij.prod.g_zero_succ,bij.prod.g_zero_zero] },
    { unfold bij.prod.succ, rw [bij.prod.g_succ] } },
  { cases x₁ with x₁,
    { unfold bij.prod.succ, rw [bij.prod.g_zero_succ] },
    { unfold bij.prod.succ, rw [bij.prod.g_succ] } }
end

def bij.prod : bijection (ℕ × ℕ) ℕ :=
    bijection.mk bij.prod.g
                 bij.prod.f
begin
  intro x,
  apply well_founded.induction diag_wf x,
  clear x,
  intros x IH,
  cases x with x₀ x₁,
  cases x₀ with x₀,
  { cases x₁,
    { simp [bij.prod.g_zero_zero,bij.prod.f_zero] },
    { rw [bij.prod.g_zero_succ,bij.prod.f_succ,IH],
      refl,
      unfold diag inv_image prod.fst prod.snd,
      apply prod.lex.left, simp, apply lt_succ_self }, },
  { rw [bij.prod.g_succ,bij.prod.f_succ,IH], refl,
    unfold diag inv_image prod.fst prod.snd,
    simp [succ_add,add_succ],
    apply prod.lex.right,
    apply lt_succ_self },
end
begin
  intro x,
  induction x with x,
  { rw [bij.prod.f_zero,bij.prod.g_zero_zero] },
  { rw [bij.prod.f_succ,bij.prod.g_prod_succ_eq_prod_succ_g,ih_1] },
end

instance : finite unit :=
  { count := 1
  , to_nat :=
      { f := λ _, fin.mk 0 $ nat.le_refl _
      , g := λ _, ()
      , inverse :=
        begin
          intros x y,
          cases y with y Py,
          cases x,
          have h' := nat.le_of_succ_le_succ Py,
          have h := nat.le_antisymm h' (nat.zero_le _),
          subst y,
          { split ; intro h₂ ; refl },
        end } }

instance finite_fin (n : ℕ) : finite (fin n) :=
  { count := n
  , to_nat := bijection.id }

instance pos_finite_fin (n : ℕ) : pos_finite (fin (succ n)) :=
  { pred_count := n
  , to_nat := bijection.id }

instance : infinite ℕ :=
  { to_nat := bijection.id }

section bijection_add

parameters {α : Type (u₀)} {α' : Type (u₁)}
parameters {β : Type (u₂)} {β' : Type (u₃)}
parameters (b₀ : bijection α β) (b₁ : bijection α' β')

def bijection.add.f : α ⊕ α' → β ⊕ β'
  | (sum.inr x) := sum.inr (b₁^.f x)
  | (sum.inl x) := sum.inl (b₀^.f x)

def bijection.add.g : β ⊕ β' → α ⊕ α'
  | (sum.inr x) := sum.inr (b₁^.g x)
  | (sum.inl x) := sum.inl (b₀^.g x)

def bijection.add
: bijection (α ⊕ α') (β ⊕ β') :=
bijection.mk bijection.add.f bijection.add.g
begin
  intro x,
  cases x with x x
  ; unfold bijection.add.f bijection.add.g
  ; rw bijection.f_inv
end
begin
  intro x,
  cases x with x x
  ; unfold bijection.add.f bijection.add.g
  ; rw bijection.g_inv
end

end bijection_add

section bijection_mul

parameters {α : Type (u₀)} {α' : Type (u₂)}
parameters {β : Type (u₁)} {β' : Type (u₃)}
parameters (b₀ : bijection α β) (b₁ : bijection α' β')

def bijection.mul.f : α × α' → β × β'
  | (x,y) := (b₀^.f x,b₁^.f y)

def bijection.mul.g : β × β' → α × α'
  | (x,y) := (b₀^.g x,b₁^.g y)

def bijection.mul
: bijection (α × α') (β × β') :=
bijection.mk bijection.mul.f bijection.mul.g
begin
  intro x ; cases x with x y,
  unfold bijection.mul.f bijection.mul.g,
  simp [bijection.f_inv]
end
begin
  intro x ; cases x with x y,
  unfold bijection.mul.f bijection.mul.g,
  simp [bijection.g_inv]
end

end bijection_mul

section bijection_map

open nat

variables {α α' : Type (u₀)}
variables {β β' γ : Type (u₁)}

def bijection.map (b : bijection α β) : bijection (list α) (list β) :=
bijection.mk (list.map b^.f) (list.map b^.g)
begin
  intro x, rw [list.map_map,bijection.f_inv',list.map_id]
end
begin
  intro x, rw [list.map_map,bijection.g_inv',list.map_id]
end

def option.map (f : α → β) : option α → option β
  | none := none
  | (some x) := some $ f x

def bijection.fmap (b : bijection α β) : bijection (option α) (option β) :=
bijection.mk (option.map b^.f) (option.map b^.g)
begin
  intro x, cases x ; unfold option.map,
  rw b^.f_inv
end
begin
  intro x, cases x ; unfold option.map,
  rw b^.g_inv
end

def prod.sum : ℕ × ℕ → ℕ
  | (x,y) := x+y

lemma prod_f_sum_le_self (n) : prod.sum (bij.prod.f n) ≤ n :=
begin
  induction n with n,
  { unfold bij.prod.f, refl },
  { unfold bij.prod.f,
    cases bij.prod.f n with x y,
    cases y with y h ; unfold bij.prod.succ prod.sum,
    { unfold prod.sum at ih_1, simp at ih_1,
      simp [succ_le_succ,ih_1] },
    { unfold prod.sum at ih_1,
      simp [add_succ] at ih_1,
      simp [succ_add], transitivity,
      apply ih_1,
      apply le_succ  } }
end

lemma prod_f_snd_le_self (n) : (bij.prod.f n)^.snd ≤ n :=
begin
  have h : (bij.prod.f n)^.snd ≤ prod.sum (bij.prod.f n),
  { cases bij.prod.f n,
    simp [prod.sum],
    apply le_add_left },
  transitivity,
  apply h,
  apply prod_f_sum_le_self
end


def concat.f : list ℕ → ℕ
  | list.nil := 0
  | (x :: xs) := succ (bij.prod.g (x,concat.f xs))

def concat.g : ℕ → list ℕ :=
  well_founded.fix nat.lt_wf $
    λ n,
     match n with
     | 0 := λ g : Π (m : ℕ), m < 0 → list ℕ, list.nil
     | (succ n') :=
       λ g : Π (m : ℕ), m < succ n' → list ℕ,
         let p := bij.prod.f n' in
         have h : p^.snd < succ n',
           begin
             apply lt_succ_of_le,
             apply prod_f_snd_le_self
           end,
         p^.fst :: g p^.snd h
     end

lemma concat.g_zero
: concat.g 0 = [] :=
begin
  unfold concat.g ,
  rw well_founded.fix_eq,
  refl
end

lemma concat.g_succ (n : ℕ)
: concat.g (succ n) = (bij.prod.f n)^.fst :: concat.g (bij.prod.f n)^.snd :=
begin
  unfold concat.g ,
  rw well_founded.fix_eq,
  refl
end

def concat : bijection (list ℕ) ℕ :=
bijection.mk concat.f concat.g
begin
  intro x,
  induction x,
  { unfold concat.f, apply concat.g_zero },
  { unfold concat.f,
    have h : ∀ x, bij.prod.f (bij.prod.g x) = x, { apply bij.prod^.f_inv },
    rw concat.g_succ,
    apply congr, apply congr_arg,
    { rw h },
    { rw h, unfold prod.snd, apply ih_1 },  }
end
begin
  intro x,
  apply nat.strong_induction_on x,
  clear x,
  intros x IH,
  cases x with x,
  { rw concat.g_zero, unfold concat.f,  },
  { rw concat.g_succ, unfold concat.f,
    rw IH,
    have h' : ∀ x, bij.prod.g (bij.prod.f x) = x, { apply bij.prod^.g_inv },
    destruct bij.prod.f x,
    intros x₀ x₁ h, simp [h],
    rw [← h,h'],
    apply lt_succ_of_le,
    apply prod_f_snd_le_self }
end

def fconcat.f (n : ℕ) : list (fin n) → ℕ
  | [] := 0
  | (x :: xs) := succ (bij.prod.pre.f _ (x,fconcat.f xs))

def fconcat.g (n : ℕ)  : ℕ → list (fin (succ n)) :=
  well_founded.fix lt_wf $
      λ x,
       match x with
        | 0 := λ _, []
        | (succ x') :=
             λ g : Π (y : ℕ), y < succ x' → list (fin (succ n)),
                  have h : (bij.prod.pre.g n x')^.snd < succ x',
                    begin
                      unfold bij.prod.pre.g prod.snd,
                      apply lt_of_le_of_lt,
                      apply nat.div_le_self,
                      apply lt_succ_self
                    end,
               (bij.prod.pre.g _ x')^.fst :: g (bij.prod.pre.g n x')^.snd h
       end

section sect

open bijection
open bij

lemma fconcat.g_zero (n : ℕ)
: fconcat.g n 0 = [] :=
begin
  unfold fconcat.g,
  rw well_founded.fix_eq,
  refl
end

lemma fconcat.g_succ (n x : ℕ)
: fconcat.g _ (succ x) = (bij.prod.pre.g _ x)^.fst :: fconcat.g n (bij.prod.pre.g n x)^.snd :=
begin
  unfold fconcat.g,
  rw well_founded.fix_eq,
  refl,
end

end sect

def fconcat (n : ℕ) : bijection (list (fin (succ n))) ℕ :=
bijection.mk (fconcat.f _) (fconcat.g n)
(begin
  intro x,
  induction x with x xs ih,
  { rw [ fconcat.f.equations._eqn_1
       , fconcat.g.equations._eqn_1
       , well_founded.fix_eq ],
    refl },
  { unfold fconcat.f,
    have h := (bij.prod.pre n)^.f_inv,
    unfold bij.prod.pre bijection.mk bijection.f bijection.g at h,
    rw fconcat.g_succ,
    apply congr, apply congr_arg,
    { cases x with x Px, cases x with x,
      rw h, rw h, },
    { rw h, unfold prod.snd, rw ih, } }
end)
(begin
  intro x,
  apply nat.strong_induction_on x,
  clear x,
  intros x ih,
  cases x with x,
  { rw fconcat.g_zero,
    refl },
  { rw fconcat.g_succ,
    unfold fconcat.f,
    apply congr_arg,
    unfold bij.prod.pre.g prod.snd,
    rw ih, unfold prod.fst bij.prod.pre.f,
    simp [mod_add_div],
    { apply lt_succ_of_le, apply nat.div_le_self } }
end)

end bijection_map

section

variables {α α' : Type (u₀)}
variables {β β' : Type (u₁)}
variables {γ : Type (u₂)}

local infixr ∘ := bij.comp
local infix + := bijection.add
local infix * := bijection.mul

def bij.option.f : option ℕ → ℕ
  | none := 0
  | (some n) := succ n
def bij.option.g : ℕ → option ℕ
  | 0 := none
  | (succ n) := some n

def bij.option : bijection (option ℕ) ℕ :=
bijection.mk bij.option.f bij.option.g
begin
  intro x, cases x ; refl
end
begin
  intro x, cases x ; refl
end

def fin.succ {n} : fin n → fin (succ n)
  | ⟨m,P⟩ := ⟨succ m,succ_lt_succ P⟩

def bij.option.fin.f {n : ℕ} : option (fin n) → fin (succ n)
  | none := 0
  | (some n) := fin.succ n
def bij.option.fin.g {n : ℕ} : fin (succ n) → option (fin n)
  | ⟨0,P⟩ := none
  | ⟨succ m,P⟩ := some ⟨m,lt_of_succ_lt_succ P⟩

lemma bij.option.fin.g_zero (n : ℕ)
: bij.option.fin.g (0 : fin $ succ n) = none :=
rfl

lemma bij.option.fin.g_succ {n : ℕ} (m : fin n)
: bij.option.fin.g (fin.succ m : fin $ succ n) = some m :=
begin
  cases m with m Pm,
  refl
end

def bij.option.fin {n : ℕ} : bijection (option (fin n)) (fin $ succ n) :=
bijection.mk bij.option.fin.f bij.option.fin.g
(begin
  intro x, cases x with x ; unfold bij.option.fin.f,
  { simp [bij.option.fin.g_zero] },
  { simp [bij.option.fin.g_succ] }
end)
(begin
  intro x, cases x with x
  ; cases x
  ; unfold bij.option.fin.g bij.option.fin.f fin.succ
  ; apply fin.eq_of_veq,
  { apply fin.zero_def, },
end)

def bij.lifted.f {t : Type u₀}
  {F : t → Type u₁} {G : t → Type u₂}
  (b : Π x : t, bijection (F x) (G x))
  (f : Π x, F x) (x : t)
: G x :=
(b x).f (f x)

def bij.lifted.g {t : Type u₀}
  {F : t → Type u₁} {G : t → Type u₂}
  (b : Π x : t, bijection (F x) (G x))
  (f : Π x, G x) (x : t)
: F x :=
(b x).g (f x)

def bij.lifted {t : Type u₀}
  {F : t → Type u₁} {G : t → Type u₂}
  (b : Π x : t, bijection (F x) (G x))
: bijection (Π x, F x) (Π x, G x) :=
bijection.mk (bij.lifted.f b) (bij.lifted.g b)
begin
  intros f,
  apply funext, intro x,
  unfold bij.lifted.f bij.lifted.g,
  apply (b x).f_inv
end
begin
  intros f,
  apply funext, intro x,
  unfold bij.lifted.f bij.lifted.g,
  apply (b x).g_inv
end

def bij.unit : bijection unit (fin 1) :=
bijection.mk (λ _, 0) (λ _, ())
begin
  intro x, cases x, refl
end
begin
  intro x, cases x,
  have h := le_of_succ_le_succ is_lt,
  have h' := le_antisymm (zero_le _) h,
  apply fin.eq_of_veq,
  unfold has_zero.zero,
  subst val,
end

instance : pos_finite unit :=
{ pred_count := 0
, to_nat := bij.unit }

instance inf_inf_inf_sum [infinite α] [infinite β] : infinite (α ⊕ β) :=
  { to_nat := bij.even_odd ∘ (infinite.to_nat α + infinite.to_nat β) }

instance inf_fin_inf_sum [infinite α] [finite β] : infinite (α ⊕ β) :=
  { to_nat := bij.sum.pre _ ∘ bij.sum.swap ∘ (infinite.to_nat α + finite.to_nat β) }

instance fin_inf_inf_sum [finite α] [infinite β] : infinite (α ⊕ β) :=
  { to_nat := bij.sum.pre _ ∘ (finite.to_nat α + infinite.to_nat β) }

instance finite_sum [finite α] [finite β] : finite (α ⊕ β) :=
  { count := _
  , to_nat := bij.sum.append _ _ ∘ (finite.to_nat α + finite.to_nat β)
  }

instance inf_inf_inf_prod [infinite α] [infinite β] : infinite (α × β) :=
  { to_nat := bij.prod ∘ (infinite.to_nat α * infinite.to_nat β) }

instance inf_fin_inf_prod [infinite α] [pos_finite β] : infinite (α × β) :=
  { to_nat := bij.prod.pre _ ∘ bij.prod.swap ∘ (infinite.to_nat α * pos_finite.to_nat β) }

instance fin_inf_inf_prod [pos_finite α] [infinite β] : infinite (α × β) :=
  { to_nat := bij.prod.pre _ ∘ (pos_finite.to_nat α * infinite.to_nat β) }

instance finite_prod [finite α] [finite β] : finite (α × β) :=
  { count := nat.mul (finite.count α) (finite.count β)
  , to_nat := bij.prod.append _ _ ∘ (finite.to_nat α * finite.to_nat β)
  }

end

section

variables {α α' : Type (u₀)}
variables {β β' : Type (u₁)}
variables {γ : Type (u₂)}

section embedded_sigma

parameters {t : Type u₀} {t' : Type u₁}
parameters {F : t → Type u₂} {G : t' → Type u₃}
parameters (bt : bijection t t')
parameters (b : Π x : t, bijection (F x) (G $ bt.f x))

def bij.embed.f
: (Σ x, F x) → (Σ x, G x)
  | ⟨x,Fx⟩ := ⟨bt.f x, (b x).f Fx⟩

def bij.embed.g
: (Σ x, G x) → (Σ x, F x)
  | ⟨x',Gx⟩ :=
have h : G _ = G _, from (congr_arg G (bt.g_inv x')).symm,
⟨bt.g x',(b _).g (cast h Gx)⟩

lemma foo_doo (x y : t) (Fx : F x)
  (H : G (bt.f x) = G (bt.f y))
  (H₀ : y = x)
  (H₁ : (b x).g ((b x).f Fx) == Fx)
: (b y).g (cast H ((b x).f Fx)) == Fx :=
begin
  cases H₀, rw cast_eq,
  apply H₁
end

def bij.embed'
: bijection (Σ x, F x) (Σ x, G x) :=
bijection.mk bij.embed.f bij.embed.g
begin
  intros x, cases x with x Fx,
  unfold bij.embed.f bij.embed.g,
  apply sigma.ext,
  { unfold sigma.fst,
    apply bt.f_inv },
  { unfold sigma.snd sigma.fst,
    intros H,
    apply foo_doo _ _ _ _ _ _ H,
    rw f_inv }
end
begin
  intros x, cases x with x Fx,
  unfold bij.embed.f bij.embed.g,
  apply sigma.ext,
  { unfold sigma.fst,
    apply bt.g_inv },
  { unfold sigma.snd sigma.fst,
    intros H,
    rw g_inv (b (bt.g x)),
    apply cast_heq, }
end

end embedded_sigma

def bij.embed {t : Type u₀}
  {F : t → Type u₁} {G : t → Type u₂}
  (b : Π x : t, bijection (F x) (G x))
: bijection (Σ x, F x) (Σ x, G x) :=
bij.embed' id b

section

parameter {t : Type u₀}
parameter {F : t → Type u₂}
parameter {sz : t → ℕ}
parameter (bt : bijection t ℕ)
parameter (b : Π x : t, bijection (F x) (fin $ succ $ sz x))

def bij.sigma_inf_fin_f : (Σ x, F x) → ℕ
  | ⟨x,Fx⟩ := fin.sum (bt.f x) (λ i, succ $ sz $ bt.g i.val) + ( (b x).f Fx ).val

def bij.sigma_inf_fin_g : ℕ → ℕ → (Σ x, F x)
  | j i :=
let x : t := bt.g i in
if h : j < succ (sz x)
then ⟨x, (b x).g ⟨_,h⟩⟩
else
  have H : j - succ (sz x) < j,
    begin
      apply sub_lt_of_pos_le,
      apply zero_lt_succ,
      apply le_of_not_gt h,
    end,
  bij.sigma_inf_fin_g (j - succ (sz x)) (succ i)

lemma bij.sigma_inf_fin_g_def
  (i j : ℕ)
:   bij.sigma_inf_fin_g i j
  = if h : i < succ (sz $ bt.g j)
    then ⟨bt.g j, (b $ bt.g j).g ⟨_,h⟩⟩
    else bij.sigma_inf_fin_g (i - succ (sz $ bt.g j)) (succ j) :=
by rw [bij.sigma_inf_fin_g.equations._eqn_1]

def next (k : ℕ) (x : t) : t :=
bt.g (bt.f x + k)

lemma next_0 (x : t)
: next 0 x = x :=
by { unfold next, simp [bijection.f_inv] }

def bij.sigma_inf_fin : bijection (Σ x, F x) ℕ :=
bijection.mk
  bij.sigma_inf_fin_f
  (λ i, bij.sigma_inf_fin_g i 0)
begin
  intros x,
  cases x with x Fx,
  revert Fx,
  unfold bij.sigma_inf_fin_f,
  have n : {n // bt.f x = n } := ⟨_,rfl⟩ ,
  cases n with n Hn,
  revert Hn,
  rw ← next_0 bt x,
  generalize : 0 = k,
  revert x,
  induction n ;
  intros x Hn Fx,
  case zero
  { simp [fin.sum_zero],
    have Hx : (bt.g k) = x,
    { apply bt.f_injective,
      simp [bt.g_inv,Hn], admit },
    admit,
    /- have H : (((b x).f Fx).val < succ (sz (bt.g k))),
    { rw Hx, apply fin.is_lt _, },
    rw [bijection.bij.sigma_inf_fin_g_def,dif_pos],
    subst x,
    apply congr_arg, symmetry,
    rw ← bijection.inverse,
    apply fin.eq_of_veq, refl, -/ },
  case succ n
  { simp [fin.sum_succ],
    -- have H : ¬ (sz (bt.g (0 : fin $ succ n).val)
    --     + (((b x).f Fx).val + fin.sum n ((λ (i : fin (succ n)), sz (bt.g (i.val))) ∘ fin.succ))
    --     < succ (sz (bt.g 0))), admit,
    rw [bijection.bij.sigma_inf_fin_g_def,dif_neg], admit, admit }
end
begin
  intros x,
  change _ = x + 0,
  have H : x + 0 = x + fin.sum 0 (λ (i : fin 0), succ $ sz (bt.g (i.val))),
  { rw fin.sum_zero },
  rw H, clear H,
  generalize : 0 = k, revert k,
  apply nat.strong_induction_on x _,
  clear x, intros x IH k,
  rw [bijection.bij.sigma_inf_fin_g_def],
  cases decidable.em (x < succ (sz (bt.g k))) with h h,
  { rw [dif_pos h],
    unfold bij.sigma_inf_fin_f,
    simp [bijection.g_inv,fin.sum_zero],
    rw [bijection.g_inv], },
  { rw [dif_neg h,IH],
    { simp [fin.sum_succ'],
      unfold function.comp,
      simp [widen_val,fin.max_def],
      rw ← nat.add_assoc,
      apply congr_fun, apply congr_arg,
      rw [← nat.add_sub_assoc,nat.add_sub_cancel_left],
      apply le_of_not_gt h },
    { apply sub_lt_of_pos_le,
      apply zero_lt_succ,
      apply le_of_not_gt h }, },
end

end

def bij.sigma_pair {t : Type u₀}
  {F : Type u₁}
: bijection (Σ x : t, F) (t × F) :=
bijection.mk' (λ x, (x.1,x.2)) (λ x, ⟨x.1,x.2⟩)
begin
  intros x y,
  cases x, cases y, simp,
  split,
  { intros H, cases H, subst fst, subst snd },
  { intros H, injection H with H₀ H₁,
    cases H₁, cases H₀, split ; refl }
end

instance infinite_sigma {t : Type u₀} (T : t → Type u₁)
  [infinite t] [∀ x, infinite (T x)]
: infinite (Σ i, T i) :=
  { to_nat :=
infinite.to_nat (t × ℕ) ∘ bij.sigma_pair ∘ bij.embed (λ x, infinite.to_nat (T x)) }

instance infinite_sigma_of_pos_finite {t : Type u₀} (T : t → Type u₁)
  [infinite t] [∀ x, pos_finite (T x)]
: infinite (Σ i, T i) :=
  { to_nat := infinite.to_nat (t × ℕ) ∘ bij.sigma_pair ∘ bij.embed (λ x, sorry ∘ pos_finite.to_nat (T x)) }

instance pos_finite_option [finite α] : pos_finite (option α) :=
 { pred_count := finite.count α
 , to_nat := bij.option.fin ∘ bijection.fmap (finite.to_nat α) }

instance infinite_option [infinite α] : infinite (option α) :=
 { to_nat := bij.option ∘ bijection.fmap (infinite.to_nat α) }

instance inf_list_of_fin [pos_finite α] : infinite (list α) :=
 { to_nat := fconcat _ ∘ bijection.map (pos_finite.to_nat α) }

instance inf_list_of_inf  [infinite α] : infinite (list α) :=
 { to_nat := concat ∘ bijection.map (infinite.to_nat α) }



def infinite_of_injective
  {f : α → ℕ}
  {g : ℕ → α}
  (Hf : function.injective f)
  (Hg : function.injective g)
: infinite α :=
sorry

def finite_of_injective {n : ℕ}
  {f : α → fin n}
  (h : function.injective f)
: finite α :=
sorry

end

end bijection
