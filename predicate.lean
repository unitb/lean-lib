
import util.logic
import util.data.fin
import util.category

namespace predicate

universe variables u u' u₀ u₁ u₂

variables {α : Type u₀}
variables {β : Type u₁}
variables {γ : Type u₂}

@[reducible]
def pred' (α : Sort u) := α → Prop

def lifted₀ : Prop → pred' α := λ p _, p
def lifted₁ (op : Prop → Prop) : pred' α → pred' α :=
λ p i, op (p i)
def lifted₂ (op : Prop → Prop → Prop) (p q : pred' α) : pred' α :=
λ i, op (p i) (q i)

def ew (p : pred' α) : Prop :=
∀ i, p i

def False : pred' α := lifted₀ false
def True : pred' α := lifted₀ true

def p_or (p₀ p₁ : pred' α) : pred' α
:= lifted₂ or p₀ p₁

@[simp]
lemma p_or_to_fun (p₀ p₁ : pred' α) (x : α)
: p_or p₀ p₁ x ↔ p₀ x ∨ p₁ x := by refl

def p_and (p₀ p₁ : pred' α) : pred' α
:= lifted₂ and p₀ p₁

@[simp]
lemma p_and_to_fun (p₀ p₁ : pred' α) (x : α)
: p_and p₀ p₁ x ↔ p₀ x ∧ p₁ x := by refl

def p_impl (p₀ p₁ : pred' α) : pred' α
:= lifted₂ implies p₀ p₁

@[simp]
lemma p_impl_to_fun (p₀ p₁ : pred' α) (x : α)
: p_impl p₀ p₁ x ↔ (p₀ x → p₁ x) := by refl


def p_entails (p₀ p₁ : pred' α) : Prop
:= ew (p_impl p₀ p₁)

lemma p_entails_of_fun (p₀ p₁ : pred' α) (x : β)
: p_entails p₀ p₁ ↔ ∀ x, p₀ x → p₁ x := by refl

def p_not (p : pred' α) : pred' α
:= lifted₁ not p

@[simp]
lemma False_eq_false (τ : β) : False τ = false := rfl
@[simp]
lemma True_eq_true (τ : β) : True τ = true := rfl

def p_exists {t : Type u} {β : Type u'} (P : t → pred' β) : pred' β :=
λ x, ∃ y, P y x

def p_forall {t : Type u} {β : Type u'} (P : t → pred' β) : pred' β :=
λ x, ∀ y, P y x

notation `∃∃` binders `, ` r:(scoped P, p_exists P) := r
notation `∀∀` binders `, ` r:(scoped P, p_forall P) := r

infixl ` || ` := p_or
infixl ` && ` := p_and
infixr ` ⟶ `:60 := p_impl
infix ` ⟹ `:60 := p_entails
notation `⦃ `:max act ` ⦄`:0 := ew act

instance : has_neg (α → Prop) := has_neg.mk p_not

@[simp]
lemma p_and_comp (p q : pred' α) (f : β → α)
: (p && q) ∘ f = (p ∘ f) && (q ∘ f) :=
rfl

@[simp]
lemma p_not_to_fun (p₀ : pred' α) (x : α)
: (- p₀) x ↔ ¬ p₀ x := by refl

lemma p_not_eq_not (p : pred' β) (τ) : ¬ p τ ↔ (-p) τ :=
by refl

@[simp]
lemma p_not_True : (- True) = (False : pred' α) :=
begin
  apply funext, intro x,
  rw [← p_not_eq_not],
  simp,
end

@[simp]
lemma p_not_False : (- False) = (True : pred' α) :=
begin
  apply funext, intro x,
  rw [← p_not_eq_not],
  simp,
end

@[simp]
lemma entails_True (p : pred' α)
: p ⟹ True :=
begin
  intro x, simp,
end


@[simp]
lemma True_p_and (p : pred' α)
: True && p = p :=
begin
  apply funext, intro x,
  simp,
end

@[simp]
lemma p_and_True (p : pred' α)
: p && True = p :=
begin
  apply funext, intro x,
  simp,
end

@[simp]
lemma True_p_or (p : pred' α)
: True || p = True :=
begin
  apply funext, intro x,
  simp,
end

@[simp]
lemma p_or_False (p : pred' α)
: p || False = p :=
begin
  apply funext, intro x,
  simp,
end


@[simp]
lemma False_p_or (p : pred' α)
: False || p = p :=
begin
  apply funext, intro x,
  simp,
end

@[refl]
lemma entails_refl (p : pred' β)
: p ⟹ p :=
assume _, id

lemma p_or_p_imp_p_or' {p p' q q' : pred' α}
  (hp : p ⟹ p')
  (hq : q ⟹ q')
: (p || q)  ⟹  (p' || q')  :=
by { intro, apply or.imp (hp _) (hq _) }

lemma p_or_p_imp_p_or {p p' q q' : pred' α} {τ}
  (hp : (p ⟶ p') τ)
  (hq : (q ⟶ q') τ)
: ( p || q ) τ → ( p' || q' ) τ :=
by apply or.imp hp hq

lemma p_and_p_imp_p_and_right' {p q q' : pred' α}
  (hq : q ⟹ q')
: ( p && q ) ⟹ ( p && q' ) :=
by { intro, apply and.imp id (hq _) }

lemma p_or_p_imp_p_or_right' {p q q' : pred' α}
  (hq : q ⟹ q')
: ( p || q ) ⟹ ( p || q' ) :=
by { intro, apply or.imp id (hq _) }

lemma p_or_p_imp_p_or_right {p q q' : pred' α} {τ}
  (hq : (q ⟶ q') τ)
: ( p || q ) τ → ( p || q' ) τ :=
by apply or.imp id hq

lemma p_or_p_imp_p_or_left {p p' q : pred' α} {τ}
  (hp : (p ⟶ p') τ)
: ( p || q ) τ → ( p' || q ) τ :=
by apply or.imp hp id

lemma p_imp_p_imp_p_imp {p p' q q' : pred' α} {τ}
  (hp : (p' ⟶ p) τ)
  (hq : (q ⟶ q') τ)
: ( p ⟶ q ) τ → ( p' ⟶ q' ) τ :=
assume hpq, hq ∘ hpq ∘ hp

lemma p_imp_entails_p_imp {p p' q q' : pred' α}
  (hp : p' ⟹ p)
  (hq : q ⟹ q')
: ( p ⟶ q ) ⟹ ( p' ⟶ q' ) :=
assume τ hpq, hq _ ∘ hpq ∘ hp _

lemma p_imp_p_imp_p_imp_left {p p' q : pred' α} {τ}
  (hp : (p' ⟶ p) τ)
: ( p ⟶ q ) τ → ( p' ⟶ q ) τ :=
p_imp_p_imp_p_imp hp id

lemma p_imp_p_imp_p_imp_right {p q q' : pred' α} {τ}
  (hq : (q ⟶ q') τ)
: ( p ⟶ q ) τ → ( p ⟶ q' ) τ :=
p_imp_p_imp_p_imp id hq

lemma p_imp_entails_p_imp_left {p p' q : pred' α}
  (hp : p' ⟹ p)
: ( p ⟶ q ) ⟹ ( p' ⟶ q ) :=
p_imp_entails_p_imp hp (by refl)

lemma entails_imp_entails_left {p p' q : pred' α}
  (hp : p' ⟹ p)
: ( p ⟹ q ) → ( p' ⟹ q ) :=
begin
  intros h τ,
  apply p_imp_entails_p_imp_left hp _ (h _),
end

lemma p_imp_entails_p_imp_right {p q q' : pred' α}
  (hq : q ⟹ q')
: ( p ⟶ q ) ⟹ ( p ⟶ q' ) :=
p_imp_entails_p_imp (by refl) hq

@[simp]
lemma p_or_self (p : pred' β) :
p || p = p :=
by { apply funext, intro, simp }

lemma p_not_p_not_iff_self (p : pred' β) :
- - p = p :=
begin
  apply funext, intro x,
  simp [not_not_iff_self],
end

lemma p_and_over_or_left (p q r : pred' β)
: p && (q || r) = (p && q) || (p && r) :=
begin
  apply funext, intro x, simp [distrib_left_and],
end

lemma p_and_over_or_right (p q r : pred' β)
: (q || r) && p = (q && p) || (r && p) :=
begin
  apply funext, intro x, simp [distrib_left_and],
end

lemma p_or_over_and_left (p q r : pred' β)
: p || (q && r) = (p || q) && (p || r) :=
begin
  apply funext, intro x, simp [distrib_right_or],
end

lemma p_or_over_and_right (p q r : pred' β)
: (q && r) || p = (q || p) && (r || p) :=
begin
  apply funext, intro x, simp [distrib_right_or],
end

lemma mutual_entails {p q : pred' β}
  (h₀ : p ⟹ q)
  (h₁ : q ⟹ p)
: p = q :=
begin
  apply funext, intro,
  rw ← iff_eq_eq,
  split,
  { apply h₀ },
  { apply h₁ },
end

@[simp]
lemma False_entails (p : pred' β)
: False ⟹ p :=
assume x, false.elim

lemma p_and_p_not_self (p : pred' β)
: p && -p = False :=
begin
  apply mutual_entails _ (False_entails _),
  intros x P,
  apply P.right P.left
end

@[simp]
lemma p_or_p_not_self (p : pred' β)
: p || -p = True :=
begin
  apply mutual_entails,
  { simp },
  { intros s _, apply classical.em }
end

lemma p_and_p_or_p_not_self (p q : pred' β)
: p && (q || -p) = p && q :=
by simp [p_and_over_or_left,p_and_p_not_self]

lemma p_not_and_self (p : pred' β)
: -p && p = False :=
begin
  apply funext, intro x, simp,
end

lemma p_not_p_and (p q : pred' β)
: - (p && q) = -p || -q :=
begin
  apply funext, intro x,
  simp [not_and_iff_not_or_not],
end

lemma p_not_p_or (p q : pred' β)
: - (p || q) = -p && -q :=
begin
  apply funext, intro x,
  simp [not_or_iff_not_and_not],
end

lemma p_not_and_self_or (p q : pred' β) :
- p && (p || q) = -p && q :=
by rw [p_and_over_or_left,p_not_and_self,False_p_or]

@[simp]
lemma p_exists_to_fun {t : Type u'} (P : t → pred' β) (i : β)
: (∃∃ x, P x) i ↔ (∃ x, P x i) :=
by refl

@[simp]
lemma p_forall_to_fun {t : Type u'} (P : t → pred' β) (i : β)
: (∀∀ x, P x) i ↔ (∀ x, P x i) :=
by refl


lemma ew_p_forall {t} (p : t → pred' β)
: ⦃ ∀∀ x, p x ⦄ ↔ ∀ x, ⦃ p x ⦄ :=
begin
  unfold ew p_forall,
  rw forall_swap,
end

lemma p_not_p_exists {t} (p : t → pred' β) :
(- ∃∃ x, p x) = (∀∀ x, -p x) :=
begin
  apply funext, intro x,
  simp [not_exists_iff_forall_not],
end

lemma p_exists_p_imp {t} (p : t → pred' β) (q : pred' β) :
(∃∃ x, p x) ⟶ q = (∀∀ x, p x ⟶ q) :=
begin
  apply funext, intro,
  simp,
  rw exists_imp_iff_forall_imp,
end

lemma p_or_comm (p q : pred' β) : p || q = q || p :=
begin apply funext, intro x, simp end

lemma p_or_assoc (p q r : pred' β) : p || (q || r) = p || q || r :=
begin apply funext, intro x, simp end

lemma p_and_comm (p q : pred' β) : p && q = q && p :=
begin apply funext, intro x, simp end

lemma p_and_assoc (p q r : pred' β) : p && (q && r) = p && q && r :=
begin apply funext, intro x, simp end

lemma p_and_p_imp (p q r : pred' β) : p && q ⟶ r = p ⟶ (q ⟶ r) :=
begin
  apply funext, intro x, simp,
  rw ← iff_eq_eq,
  split
  ; intros h h' ; intros
  ; apply h
  ; try { split }
  ; try { cases h' }
  ; assumption
end

@[simp]
lemma p_or_intro_left (p q : pred' β)
: p ⟹ p || q :=
assume _, or.intro_left _

@[simp]
lemma p_or_intro_right (p q : pred' β)
: q ⟹ p || q :=
assume _, or.intro_right _

lemma p_or_entails_of_entails {p q r : pred' β}
  (h₀ : p ⟹ r)
  (h₁ : q ⟹ r)
: p || q ⟹ r :=
assume _, or.rec (h₀ _) (h₁ _)

lemma entails_p_or_of_entails_left {p q r : pred' β}
  (h₀ : p ⟹ q)
: p ⟹ q || r :=
assume x, (or.intro_left _) ∘ (h₀ x)

lemma entails_p_or_of_entails_right {p q r : pred' β}
  (h₀ : p ⟹ r)
: p ⟹ q || r :=
assume x, (or.intro_right _) ∘ (h₀ x)

lemma entails_p_and_of_entails {p q r : pred' β}
  (h₀ : p ⟹ q)
  (h₁ : p ⟹ r)
: p ⟹ q && r :=
assume x Hp, ⟨h₀ _ Hp,h₁ _ Hp⟩

lemma p_and_entails_of_entails_left {p q r : pred' β}
  (h₁ : p ⟹ r)
: p && q ⟹ r :=
assume x Hp, h₁ _ Hp.left

lemma p_and_entails_of_entails_right {p q r : pred' β}
  (h₁ : q ⟹ r)
: p && q ⟹ r :=
assume x Hp, h₁ _ Hp.right

@[simp]
lemma p_and_elim_left (p q : pred' β)
: p && q ⟹ p :=
assume x, and.left

@[simp]
lemma p_and_elim_right (p q : pred' β)
: p && q ⟹ q :=
assume x, and.right

@[trans]
lemma entails_trans {p : pred' β} (q : pred' β) {r : pred' β}
  (h₀ : p ⟹ q)
  (h₁ : q ⟹ r)
: p ⟹ r :=
assume x, h₁ x ∘ h₀ x

lemma p_not_comp (p : pred' α) (f : β → α)
: (-(p ∘ f) : pred' β) = (-p : pred' α) ∘ f :=
by { apply funext, intro, refl }

lemma comp_entails_comp {p q : pred' β} (f : α → β)
  (H : p ⟹ q)
: p ∘ f ⟹ q ∘ f :=
assume x, H (f x)

lemma p_and_entails_p_and_left (p q x : pred' β)
  (h : p ⟹ q)
: p && x ⟹ q && x :=
assume x, and.imp_left (h x)

lemma p_and_entails_p_and_right {p q : pred' β} (x : pred' β)
  (h : p ⟹ q)
: x && p ⟹ x && q :=
assume x, and.imp_right (h x)

lemma p_not_entails_p_not_right {p q : pred' β}
  (h : q ⟹ p)
: - p ⟹ - q :=
assume x, mt (h x)

lemma entails_of_eq (p q : pred' β)
  (h : p = q)
: p ⟹ q :=
by simp [h]

lemma p_and_entails_p_or (p q : pred' β)
: p && q ⟹ p || q :=
assume x, or.intro_left _ ∘ and.left

lemma True_p_imp (p : pred' β)
: True ⟶ p = p :=
begin
  apply funext, intro, rw [← iff_eq_eq],
  split
  ; intro h
  ; try { intro }
  ; apply h,
  trivial
end

lemma ew_eq_true {p : pred' β} : ⦃ p ⦄ → p = True :=
begin
  intros h,
  apply funext, intro x,
  simp [eq_true],
  apply h
end

lemma ew_imp_ew {p q : pred' β}
  (H : p ⟹ q)
: ⦃ p ⦄ → ⦃ q ⦄ :=
forall_imp_forall H

lemma p_or_over_p_exists_left {t} (p : t → pred' β) (q : pred' β) {w : t → pred' β}
  (h : ⦃ ∃∃ x : t, w x ⦄)
: q || (∃∃ x, p x) = (∃∃ x, q || p x) :=
begin
  apply funext, intro,
  have _inst : nonempty t := nonempty_of_exists (h x),
  simp [distrib_or_over_exists_left]
end

lemma p_and_over_p_exists_right {t} (p : t → pred' β) (q : pred' β)
: (∃∃ x, p x) && q = (∃∃ x, p x && q) :=
begin
  apply funext, intro i,
  rw ← iff_eq_eq,
  simp,
  split
  ; intro h
  ; cases h with x y
  ; cases y with y h
  ; exact ⟨y,x,h⟩,
end

lemma shunting (p q r : pred' β)
: p ⟶ q || r = (p && - q) ⟶ r :=
begin
  apply funext, intro i,
  simp, rw ← iff_eq_eq,
  split ; intros h₀ h₁,
  { cases h₁ with h₁ h₂,
    cases h₀ h₁ with h₃ h₃,
    { cases h₂ h₃ },
    { apply h₃ } },
  { cases classical.em (q i) with h₂ h₂,
    { left, apply h₂ },
    { right, apply h₀, exact ⟨h₁,h₂⟩ } }
end

lemma p_not_p_imp (p q : pred' β)
: (-p) ⟶ q = p || q :=
begin
  rw [← True_p_and (-p),← shunting,True_p_imp],
end

lemma p_or_entails_p_or_right (p q x : pred' β)
: p ⟹ q → x || p ⟹ x || q :=
begin
  intros h i, simp,
  apply or.imp_left (h _),
end

lemma p_or_entails_p_or {p p' q q' : pred' β}
  (H₀ : p  ⟹ q )
  (H₁ : p' ⟹ q')
: p || p' ⟹ q || q' :=
assume i, or.imp (H₀ _) (H₁ _)

lemma p_or_not_and (p q : pred' β)
: p || (- p && q) = p || q :=
begin
  apply funext, intro,
  simp,
  rw [← or_not_and (p _) (q _)],
  simp
end

lemma p_exists_intro {t : Type u'} {p : t → pred' β} (x : t)
: p x ⟹ (∃∃ x, p x) :=
assume s h, ⟨x,h⟩

lemma p_exists_elim {t : Type u'} {p : t → pred' β} {q : pred' β}
  (H : ∀ x, p x ⟹ q)
: (∃∃ x, p x) ⟹ q :=
assume s h, exists.elim h (λ x, H x s)

lemma p_exists_entails_p_exists {t : Type u'} (p q : t → pred' β)
: (∀ x, p x ⟹ q x) → (∃∃ x, p x) ⟹ (∃∃ x, q x) :=
begin
  intros h i,
  simp,
  apply exists_imp_exists,
  intro,
  apply h
end

lemma p_exists_entails_p_exists' {t : Type u₀} {t' : Type u₁}
  (p : t → pred' β)
  (q : t' → pred' β)
  (f : t → t')
  (h : (∀ x, p x ⟹ q (f x)))
: (∃∃ x, p x) ⟹ (∃∃ x, q x) :=
begin
  intros h' h'',
  simp,
  apply exists_imp_exists',
  intro,
  apply h a,
  apply h''
end

lemma p_exists_imp_eq_p_forall_imp
  (p : α → pred' β) (q : pred' β)
: ((∃∃ x, p x) ⟶ q) = (∀∀ x, p x ⟶ q) :=
begin
  apply funext, intro i,
  simp [exists_imp_iff_forall_imp],
end

lemma p_exists_entails_eq_p_forall_entails
  (p : α → pred' β) (q : pred' β)
: ((∃∃ x, p x) ⟹ q) ↔ (∀ x, p x ⟹ q) :=
begin
  unfold p_entails ew,
  rw forall_swap,
  simp [p_exists_imp_eq_p_forall_imp],
end

lemma p_exists_variable_change
  (p : α → pred' β) (q : γ → pred' β)
  (f : α → γ)
  (g : γ → α)
  (Hf : ∀ i, p i ⟹ q (f i))
  (Hg : ∀ j, q j ⟹ p (g j))
: (∃∃ i, p i) = (∃∃ j, q j) :=
begin
  apply funext, intro i, simp,
  unfold p_entails at Hf Hg,
  rw [← ew_p_forall] at Hf Hg,
  rw exists_variable_change _ _ f g,
  apply Hf,
  apply Hg,
end

lemma p_exists_range_subtype {α : Type u}
  (p : α → Prop) (q : α → pred' β)
: (∃∃ i, (λ _, p i) && q i) = (∃∃ j : subtype p, q j) :=
begin
  apply funext, intro i, simp,
  rw exists_range_subtype
end

@[congr]
lemma p_exists_congr {p q : α → pred' β}
  (h : ∀ i, p i = q i)
: p_exists p = p_exists q :=
begin
  apply funext, intro,
  simp,
  rw exists_congr,
  intro, rw h,
end

lemma p_or_iff_not_imp (p q : pred' β)
: p || q = - p ⟶ q :=
begin
  apply funext, intro i,
  simp [or_iff_not_imp],
end

lemma p_forall_fin_zero (p : fin 0 → pred' β)
: (∀∀ i, p i) = True :=
begin
  apply funext, intro,
  simp [forall_fin_zero_iff_true],
end

lemma p_forall_split_one {n : ℕ} (p : fin (nat.succ n) → pred' β)
: (∀∀ i, p i) = p fin.max && (∀∀ i, restr p i) :=
begin
  apply funext, intro,
  simp [forall_split_one],
  refl,
end

lemma p_exists_split_one {n : ℕ} (p : fin (nat.succ n) → pred' β)
: (∃∃ i, p i) = p fin.max || (∃∃ i, restr p i) :=
begin
  apply funext, intro,
  simp [exists_split_one],
  refl,
end

instance entails_category {α} : category (@p_entails α) :=
  { ident := by { intro, refl }
  , comp  := by { intros _ _ _, apply flip (entails_trans _) }
  , assoc := by { intros, refl }
  , left_ident  := by { intros, refl }
  , right_ident := by { intros, refl } }

end predicate

-- TODO:
--   * switch definition of pred' to a record to strengthen encapsulation
--   * use τ ⊧ []φ instead of ([]φ) τ
