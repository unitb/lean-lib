import util.meta.tactic
import util.logic

import data.stream

universes u v w

open nat function

namespace coind

variables {α : Type u}
variables (β : α → Type v)

/-
coinductive ind {α : Type u} (β : α → Type v) : Type (max u v)
| intro : ∀ a, (β a → ind) → ind
-/

inductive cofix' : ℕ → Type (max u v)
| continue : cofix' 0
| intro {n} : ∀ a, (β a → cofix' n) → cofix' (n+1)

variables {β}

def head' : Π {n}, cofix' β (succ n) → α
 | n (cofix'.intro i _) := i

def children' : Π {n} (x : cofix' β (succ n)), (β (head' x) → cofix' β n)
 | n (cofix'.intro _ f) := f

def agree
: ∀ {n : ℕ}, cofix' β n → cofix' β (n+1) → Prop
 | 0 continue _ := true
 | n (cofix'.intro x y) (cofix'.intro x' y') :=
   ∃ h : x = x', ∀ i j : β _, i == j → agree (y i) (y' j)

lemma agree_def {n : ℕ} (x : cofix' β (succ n)) (y : cofix' β (succ n+1))
  (h₀ : head' x = head' y)
  (h₁ : ∀ (i : β _) (j : β _), i == j → agree (children' x i) (children' y j))
: agree x y :=
begin
  cases x, cases y,
  unfold agree,
  cases h₀,
  existsi rfl,
  unfold children' at h₁,
  intro, apply h₁,
end

lemma agree_children {n : ℕ} (x : cofix' β (succ n)) (y : cofix' β (succ n+1))
  {i j}
  (h₀ : i == j)
  (h₁ : agree x y)
: agree (children' x i) (children' y j) :=
begin
  cases x, cases y,
  unfold agree at h₁,
  cases h₁ with h h₁, subst x_a,
  unfold children',
  cases h₀, apply h₁,
  assumption,
end

def truncate {α : Type u} {β : α → Type v}
: ∀ {n : ℕ}, cofix' β (n+1) → cofix' β n
 | 0 (cofix'.intro _ _) := cofix'.continue _
 | (succ n) (cofix'.intro i f) := cofix'.intro i $ truncate ∘ f

structure cofix  {α : Type u} (β : α → Type v) : Type (max u v) :=
  (approx : ∀ n, cofix' β n)
  (consistent : ∀ n, agree (approx n) (approx $ n+1))

lemma truncate_eq_of_agree {α : Type u} {β : α → Type v} {n : ℕ}
  (x : cofix' β n)
  (y : cofix' β (succ n))
  (h : agree x y)
: truncate y = x :=
begin
  revert x y,
  induction n
  ; intros x y
  ; cases x ; cases y,
  { intro h', refl },
  { simp [agree,truncate,exists_imp_iff_forall_imp],
    introv h₀ h₁,
    subst x_a, split, refl,
    apply heq_of_eq, funext y, unfold comp,
    apply n_ih,
    apply h₁, refl }
end

variables {X : Type w}
variables (f : X → Σ y, β y → X)

def s_corec : Π (i : X) n, cofix' β n
 | _ 0 := cofix'.continue _
 | j (succ n) :=
   let ⟨y,g⟩ := f j in
   cofix'.intro y (λ i, s_corec (g i) _)

lemma P_corec (i : X) (n : ℕ) : agree (s_corec f i n) (s_corec f i (n + 1)) :=
begin
  revert i,
  induction n with n ; intro i,
  trivial,
  cases h : f i with y g,
  simp [s_corec,h,s_corec._match_1,agree] at ⊢ n_ih,
  introv h',
  cases h',
  apply n_ih,
end

protected def corec (i : X) : cofix β :=
{ approx := s_corec f i
, consistent := P_corec _ _ }

lemma head_succ' (n) (x : cofix β)
: head' (x.approx (succ n)) = head' (x.approx 1) :=
begin
  cases x, simp,
  cases h₀ : x_approx (succ n) with _ i₀ f₀,
  cases h₁ : x_approx 1 with _ i₁ f₁,
  simp [head'],
  induction n with n,
  { rw h₁ at h₀, cases h₀, trivial },
  { have H := x_consistent (succ n),
    cases h₂ : x_approx (succ n) with _ i₂ f₂,
    rw [h₀,h₂] at H,
    apply n_ih (truncate ∘ f₀),
    rw h₂,
    unfold agree at H,
    cases H with h H, cases h,
    congr, funext j, unfold comp,
    rw truncate_eq_of_agree,
    apply H, refl }
end

def head : cofix β → α
 | ⟨ x, _ ⟩ := head' (x 1)

def children : Π (x : cofix β), (β (head x) → cofix β)
 | ⟨ x, P ⟩ i :=
let H := λ n : ℕ, @head_succ' _ _ n {approx := x, consistent := P} in
{ approx := λ n, children' (x _) (cast (congr_arg _ $ by simp [head,H]) i)
, consistent :=
  begin
    intro,
    have P' := P (succ n),
    apply agree_children _ _ _ P',
    transitivity i,
    apply cast_heq,
    symmetry,
    apply cast_heq,
  end }

protected def s_mk (x : α) (ch : β x → cofix β) : Π n, cofix' β n
 | 0 :=  cofix'.continue _
 | (succ n) := cofix'.intro x (λ i, (ch i).approx n)

protected def P_mk  (x : α) (ch : β x → cofix β)
: ∀ (n : ℕ), agree (coind.s_mk x ch n) (coind.s_mk x ch (n + 1))
 | 0 := by unfold coind.s_mk
 | (succ n) := by { unfold coind.s_mk agree,
                    existsi rfl,
                    introv h, cases h,
                    apply (ch i).consistent }

protected def mk (x : α) (ch : β x → cofix β) : cofix β :=
{ approx := coind.s_mk x ch
, consistent := coind.P_mk x ch }

@[simp]
lemma children_mk (x : α) (ch : β x → cofix β)
: children (coind.mk x ch) = ch :=
begin
  funext i,
  dsimp [coind.mk,children],
  cases h : ch i,
  congr,
  funext n,
  dsimp [coind.s_mk,children',cast_eq],
  rw h,
end

lemma mk_head_children (x : cofix β)
: x = coind.mk (head x) (children x) :=
begin
  cases x,
  unfold coind.mk,
  congr,
  funext n,
  induction n with n,
  { unfold coind.s_mk, cases x_approx 0, refl },
  unfold coind.s_mk,
  cases h : x_approx (succ n) with _ hd ch,
  simp [children],
  split,
  { unfold head,
    change x_approx with ({ cofix . approx := x_approx, consistent := x_consistent}).approx,
    rw ← head_succ' n,
    change _ = (head' $ x_approx (succ n)),
    rw h, refl },
  { change ch with children' (cofix'.intro hd ch),
    clear n_ih,
    apply hfunext,
    { unfold head, rw [← h,head_succ' n ⟨x_approx,x_consistent⟩] },
    introv h',
    congr, rw h,
    transitivity y, apply h',
    symmetry, apply cast_heq, },
end

protected def cases {r : cofix β → Sort w}
  (f : ∀ (i : α) (c : β i → cofix β), r (coind.mk i c)) (x : cofix β) : r x :=
suffices r (coind.mk (head x) (children x)),
  by { rw [mk_head_children x], exact this },
f (head x) (children x)

protected def cases_on {r : cofix β → Sort w}
    (x : cofix β) (f : ∀ (i : α) (c : β i → cofix β), r (coind.mk i c)) : r x :=
coind.cases f x

@[simp]
lemma head_mk (x : α) (ch : β x → cofix β)
: head (coind.mk x ch) = x :=
rfl

inductive path : cofix β → list (Σ i, β i) → Type (max u v)
 | nil (x : cofix β) : path x []
 | child (xs : list (Σ i, β i)) {y : α} (i : β y) (ch : β y → cofix β)
   : path (ch i) xs → path (coind.mk y ch) (⟨ y, i ⟩ :: xs)

def select : ∀ {x : cofix β} {ps}, path x ps → cofix β
 | ._ ._ (path.nil x) := x
 | ._ ._ (path.child xs i ch ps) := select ps

inductive nested (x : cofix β) : cofix β → list (Σ i, β i) → Prop
 | rfl {} : nested x []
 | child (xs : list (Σ i, β i)) {y : α} (i : β y) (ch : β y → cofix β)
   : nested (ch i) xs → nested (coind.mk y ch) (⟨ y, i ⟩ :: xs)

lemma ext (x y : cofix β)
  (H : ∀ (ps) (Hx : path x ps) (Hy : path y ps), head (select Hx) = head (select Hy))
: x = y :=
sorry

section bisim
  variable (R : cofix β → cofix β → Prop)
  local infix ~ := R

  def is_bisimulation :=
      ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ →
        head s₁ = head s₂ ∧
        (∀ i j : β (head _), i == j → children s₁ i ~ children s₂ j)

  theorem nth_of_bisim (bisim : is_bisimulation R) :
     ∀ {s₁ s₂} ps (p₁ : path s₁ ps) (p₂ : path s₂ ps),
       s₁ ~ s₂ →
         head (select p₁) = head (select p₂) ∧
         ∀ i j, i == j →
                children (select p₁) i ~ children (select p₂) j :=
  begin
    intros _ _ _,
    revert s₁ s₂,
    induction ps,
    { introv h₀,
      have h₁ := bisim h₀,
      cases p₁, cases p₂, simp [select],
      apply h₁, },
    { introv h₀,
      cases p₁, cases p₂,
      unfold select,
      apply ps_ih p₁_a p₂_a,
      have h₁ := (bisim h₀).right p₁_i p₁_i heq.rfl,
      have h₂ := @children_mk _ β,
      dunfold coind.mk at h₂,
      simp [h₂] at h₁, apply h₁, }
  end

  -- If two streams are bisimilar, then they are equal
  theorem eq_of_bisim (bisim : is_bisimulation R) : ∀ {s₁ s₂}, s₁ ~ s₂ → s₁ = s₂ :=
  begin
    introv Hr, apply ext,
    introv,
    have H := nth_of_bisim R bisim ps Hx Hy Hr,
    apply H.left
  end
end bisim

section coinduction

variables β
def R (s₁ s₂ : cofix β) :=
   head s₁ = head s₂ ∧
            ∀ -- (γ : cofix β → Type u)
              -- (φ : ∀ x : cofix β, γ x)
              (φ : Π x : cofix β, Type v)
              (γ : Π x : cofix β, φ x → Type u)
              (fr : ∀ (x : cofix β) i, γ x i),
              -- (I : Π x : cofix β, β (head x))
              (∀ i₂ j₂, i₂ == j₂ → fr s₁ i₂ == fr s₂ j₂) →
              ∀ i j i' j',
                i  == j →
                i' == j' →
                fr (children s₁ i) i' == fr (children s₂ j) j'

lemma R_is_bisimulation : is_bisimulation (R β) :=
sorry

variables {β}

lemma coinduction {s₁ s₂ : cofix β}
  (hh : head s₁ = head s₂)
  (ht : ∀ (γ : Type u) (fr : cofix β → γ),
          fr s₁ = fr s₂ →
          ∀ i j, i == j →
                 fr (children s₁ i) = fr (children s₂ j))
: s₁ = s₂ :=
eq_of_bisim
  (R β) (R_is_bisimulation β)
  (and.intro hh $
   sorry)

end coinduction
end coind
