import util.meta.tactic
import util.logic

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

def index' : Π {n}, cofix' β (succ n) → α
 | n (cofix'.intro i _) := i

def children' : Π {n} (x : cofix' β (succ n)), (β (index' x) → cofix' β n)
 | n (cofix'.intro _ f) := f

def agree
: ∀ {n : ℕ}, cofix' β n → cofix' β (n+1) → Prop
 | 0 continue _ := true
 | n (cofix'.intro x y) (cofix'.intro x' y') :=
   ∃ h : x = x', ∀ i : β x', agree (y $ cast (by rw h) i) (y' i)

lemma agree_def {n : ℕ} (x : cofix' β (succ n)) (y : cofix' β (succ n+1))
  (h₀ : index' x = index' y)
  (h₁ : ∀ (i : β _) (j : β _), i == j → agree (children' x i) (children' y j))
: agree x y :=
begin
  cases x, cases y,
  unfold agree,
  cases h₀,
  existsi rfl,
  unfold children' at h₁,
  intro, apply h₁,
  apply cast_heq,
end

lemma agree_children {n : ℕ} (x : cofix' β (succ n)) (y : cofix' β (succ n+1))
  {i j}
  (h₀ : i == j)
  (h₁ : agree x y)
: agree (children' x i) (children' y j) :=
begin
  cases x, cases y,
  unfold agree at h₁,
  cases h₁ with h h₁, subst a_2,
  unfold children',
  cases h₀, apply h₁,
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
    introv h, cases x,
    congr, funext y, unfold comp,
    apply ih_1,
    apply h }
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
  simp [s_corec,h,s_corec._match_1,agree] at ⊢ ih_1,
  existsi rfl,
  intro, rw cast_eq,
  apply ih_1,
end

protected def corec (i : X) : cofix β :=
{ approx := s_corec f i
, consistent := P_corec _ _ }

lemma index_succ' {n} (x : cofix β)
: index' (x.approx (succ n)) = index' (x.approx 1) :=
begin
  cases x, simp,
  cases h₀ : approx (succ n) with _ i₀ f₀,
  cases h₁ : approx 1 with _ i₁ f₁,
  simp [index'],
  induction n with n,
  { rw h₁ at h₀, cases h₀, trivial },
  { have H := consistent (succ n),
    cases h₂ : approx (succ n) with _ i₂ f₂,
    rw [h₀,h₂] at H,
    apply ih_1 (truncate ∘ f₀),
    rw h₂,
    unfold agree at H,
    cases H with h H, cases h,
    congr, funext j, unfold comp,
    simp [truncate_eq_of_agree _ _ (H j),cast_eq], }
end

def index : cofix β → α
 | ⟨ x, _ ⟩ := index' (x 1)

def children : Π (x : cofix β), (β (index x) → cofix β)
 | ⟨ x, P ⟩ i :=
have H : _, from λ n : ℕ, @index_succ' _ _ n {approx := x, consistent := P},
{ approx := λ n, children' (x _) (cast (congr_arg _ $ by simp [index,H]) i)
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

protected def cases {r : Type w}
  (f : ∀ (i : α), (β i → cofix β) → r) (x : cofix β) : r :=
f (index x) (children x)

protected def cases_on {r : Type w} (x : cofix β) (f : ∀ (i : α), (β i → cofix β) → r) : r :=
coind.cases f x

end coind
