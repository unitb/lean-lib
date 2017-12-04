
import util.logic
import util.data.fin
import util.category
import util.meta.tactic.basic
import util.meta.tactic.monotonicity

namespace predicate

universe variables u u' u₀ u₁ u₂

variables {α : Sort u₀}
variables {β : Sort u₁}
variables {γ : Sort u₂}

-- @[reducible]
structure pred' (α : Sort u) : Type u :=
  (apply : α → Prop)

instance : has_coe_to_fun (pred' α) := ⟨ _, pred'.apply ⟩

def contramap : pred' α → (β → α) → pred' β
 | ⟨ p ⟩ f := ⟨ p ∘ f ⟩

infixr ` '∘ `:90 := contramap

@[simp]
lemma contramap_apply (p : pred' α) (f : β → α) (x : β)
: (p '∘ f) x = p (f x) :=
by { cases p , refl }

def lifted₀ (p : Prop) : pred' α := ⟨ λ _, p ⟩
def lifted₁ (op : Prop → Prop) (p : pred' α) : pred' α :=
⟨ λ i, op (p i) ⟩
def lifted₂ (op : Prop → Prop → Prop) (p q : pred' α) : pred' α :=
⟨ λ i, op (p i) (q i) ⟩

def ew (p : pred' α) : Prop :=
∀ i, p i

def False {α} : pred' α := lifted₀ false
def True {α} : pred' α := lifted₀ true

def p_or (p₀ p₁ : pred' α) : pred' α :=
lifted₂ or p₀ p₁

@[simp]
lemma p_or_to_fun (p₀ p₁ : pred' α) (x : α)
: p_or p₀ p₁ x ↔ p₀ x ∨ p₁ x := by refl

def p_and (p₀ p₁ : pred' α) : pred' α :=
lifted₂ and p₀ p₁

@[simp]
lemma p_and_to_fun (p₀ p₁ : pred' α) (x : α)
: p_and p₀ p₁ x ↔ p₀ x ∧ p₁ x := by refl

def p_impl (p₀ p₁ : pred' α) : pred' α :=
lifted₂ implies p₀ p₁

@[simp]
lemma p_impl_to_fun (p₀ p₁ : pred' α) (x : α)
: p_impl p₀ p₁ x ↔ (p₀ x → p₁ x) := by refl

def p_entails (p₀ p₁ : pred' α) : Prop :=
ew (p_impl p₀ p₁)

lemma p_entails_of_fun (p₀ p₁ : pred' α) (x : β)
: p_entails p₀ p₁ ↔ ∀ x, p₀ x → p₁ x := by refl

def p_not (p : pred' α) : pred' α :=
lifted₁ not p

@[simp]
lemma False_eq_false (τ : β) : @False β τ = false := rfl
@[simp]
lemma True_eq_true (τ : β) : @True β τ = true := rfl

def pred.p_exists {β : Sort u'} {t : Sort u} (P : t → pred' β) : pred' β :=
⟨λ x, ∃ y, P y x⟩

class has_p_exists (α : Sort u) (β : Sort u') :=
  (p_exists : (β → α) → α)

instance pred_has_p_exists {α : Sort u} {β : Sort u'} : has_p_exists (pred' α) β :=
⟨ @pred.p_exists _ _ ⟩

export has_p_exists (p_exists)

def p_forall {t : Sort u} {β : Sort u'} (P : t → pred' β) : pred' β :=
⟨ λ x, ∀ y, P y x ⟩

notation `∃∃` binders `, ` r:(scoped P, p_exists P) := r
notation `∀∀` binders `, ` r:(scoped P, p_forall P) := r

instance : has_coe Prop (pred' α) :=
⟨ lifted₀ ⟩

instance to_prop_to_pred : has_coe (α → Prop) (pred' α) :=
⟨ pred'.mk ⟩

@[simp]
lemma coe_apply (p : Prop) (x : β)
: (p : pred' β) x ↔ p :=
by { unfold_coes, simp [lifted₀,pred'.apply] }

infixl ` ⋁ `:65 := p_or
infixl ` ⋀ `:70 := p_and
infixr ` ⟶ `:60 := p_impl
infix ` ⟹ `:60 := p_entails
notation `⦃ `:max act ` ⦄`:0 := ew act

instance : has_neg (pred' α) := has_neg.mk p_not

@[extensionality]
lemma pred_ext {p q : pred' α}
  (h : ∀ x, p x ↔ q x)
: p = q :=
begin
  cases p, cases q,
  congr, funext y,
  unfold_coes at h, unfold pred'.apply at h,
  simp [h y],
end

section
open tactic.interactive interactive interactive.types
     tactic (simp_arg_list)
meta def lifted_pred (rs : parse simp_arg_list) : tactic unit :=
do `[apply pred_ext, intro], simp ff rs [] (loc.ns [none])
run_cmd add_interactive [`lifted_pred]
end
@[simp]
lemma p_and_comp (p q : pred' α) (f : β → α)
: ((p ⋀ q) '∘ f) = (p '∘ f) ⋀ (q '∘ f) :=
by lifted_pred

@[simp]
lemma p_not_to_fun (p₀ : pred' α) (x : α)
: (- p₀) x ↔ ¬ p₀ x := by { refl, }

lemma p_not_eq_not (p : pred' β) (x : β) : ¬ p x ↔ (-p) x :=
by refl

@[simp]
lemma p_not_True : (- True : pred' α) = (False) :=
by lifted_pred

@[simp]
lemma p_not_False : (- False : pred' α) = True :=
by lifted_pred

-- @[simp]
-- lemma entails_True (p q : pred' α)
-- : p ⟹ q ↔ (∀ h, h ⟹ p → h ⟹ q) :=
-- begin
--   split ; intro h,
--   { intros h₀ h₁, },
-- end

@[simp]
lemma entails_True (p : pred' α)
: p ⟹ True :=
begin
  intro x, simp,
end


@[simp]
lemma True_p_and (p : pred' α)
: True ⋀ p = p :=
by lifted_pred

@[simp]
lemma p_and_True (p : pred' α)
: p ⋀ True = p :=
by lifted_pred

@[simp]
lemma True_p_or (p : pred' α)
: True ⋁ p = True :=
by lifted_pred

@[simp]
lemma p_or_False (p : pred' α)
: p ⋁ False = p :=
by lifted_pred

@[simp]
lemma False_p_or (p : pred' α)
: False ⋁ p = p :=
by lifted_pred

@[refl]
lemma entails_refl (p : pred' β)
: p ⟹ p :=
assume _, id

lemma p_or_p_imp_p_or' {p p' q q' : pred' α}
  (hp : p ⟹ p')
  (hq : q ⟹ q')
: (p ⋁ q)  ⟹  (p' ⋁ q')  :=
by { intro, apply or.imp (hp _) (hq _) }

lemma p_or_p_imp_p_or {p p' q q' : pred' α} {τ}
  (hp : (p ⟶ p') τ)
  (hq : (q ⟶ q') τ)
: ( p ⋁ q ) τ → ( p' ⋁ q' ) τ :=
by apply or.imp hp hq

@[monotonic]
lemma p_and_p_imp_p_and_right' {p q q' : pred' α}
  (hq : q ⟹ q')
: ( p ⋀ q ) ⟹ ( p ⋀ q' ) :=
by { intro, apply and.imp id (hq _) }

@[monotonic]
lemma p_or_p_imp_p_or_right' {p q q' : pred' α}
  (hq : q ⟹ q')
: ( p ⋁ q ) ⟹ ( p ⋁ q' ) :=
by { intro, apply or.imp id (hq _) }

lemma p_or_p_imp_p_or_right {p q q' : pred' α} {τ}
  (hq : (q ⟶ q') τ)
: ( p ⋁ q ) τ → ( p ⋁ q' ) τ :=
by apply or.imp id hq

lemma p_or_p_imp_p_or_left {p p' q : pred' α} {τ}
  (hp : (p ⟶ p') τ)
: ( p ⋁ q ) τ → ( p' ⋁ q ) τ :=
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


@[monotonic]
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

@[monotonic]
lemma p_imp_entails_p_imp_right {p q q' : pred' α}
  (hq : q ⟹ q')
: ( p ⟶ q ) ⟹ ( p ⟶ q' ) :=
p_imp_entails_p_imp (by refl) hq

@[simp]
lemma p_or_self (p : pred' β) :
p ⋁ p = p :=
by lifted_pred

lemma p_not_p_not_iff_self (p : pred' β) :
- - p = p :=
by lifted_pred [not_not_iff_self]


lemma p_and_over_or_left (p q r : pred' β)
: p ⋀ (q ⋁ r) = (p ⋀ q) ⋁ (p ⋀ r) :=
begin
  apply pred_ext, intro x, simp [distrib_left_and],
end

lemma p_and_over_or_right (p q r : pred' β)
: (q ⋁ r) ⋀ p = (q ⋀ p) ⋁ (r ⋀ p) :=
begin
  apply pred_ext, intro x, simp [distrib_left_and],
end

instance : is_left_distrib (pred' β) (⋀) (⋁) :=
⟨ p_and_over_or_left ⟩
instance : is_right_distrib (pred' β) (⋀) (⋁) :=
⟨ by { intros, apply p_and_over_or_right } ⟩

lemma p_or_over_and_left (p q r : pred' β)
: p ⋁ (q ⋀ r) = (p ⋁ q) ⋀ (p ⋁ r) :=
begin
  apply pred_ext, intro x, simp [distrib_right_or],
end

lemma p_or_over_and_right (p q r : pred' β)
: (q ⋀ r) ⋁ p = (q ⋁ p) ⋀ (r ⋁ p) :=
by lifted_pred [distrib_right_or]

instance is_left_distrib_or_and : is_left_distrib (pred' β) (⋁) (⋀) :=
⟨ p_or_over_and_left ⟩
instance is_right_distrib_or_and : is_right_distrib (pred' β) (⋁) (⋀) :=
⟨ by { intros, apply p_or_over_and_right } ⟩

lemma mutual_entails {p q : pred' β}
  (h₀ : p ⟹ q)
  (h₁ : q ⟹ p)
: p = q :=
begin
  apply pred_ext, intro,
  split,
  { apply h₀ },
  { apply h₁ },
end

@[simp]
lemma False_entails (p : pred' β)
: False ⟹ p :=
assume x, false.elim

lemma p_and_p_not_self (p : pred' β)
: p ⋀ -p = False :=
begin
  apply mutual_entails _ (False_entails _),
  intros x P,
  apply P.right P.left
end

@[simp]
lemma p_or_p_not_self (p : pred' β)
: p ⋁ -p = True :=
begin
  apply mutual_entails,
  { simp },
  { intros s _, apply classical.em }
end

lemma p_and_p_or_p_not_self (p q : pred' β)
: p ⋀ (q ⋁ -p) = p ⋀ q :=
by simp [p_and_over_or_left,p_and_p_not_self]

lemma p_not_and_self (p : pred' β)
: (-p) ⋀ p = @False β :=
begin
  apply pred_ext, intro x, simp,
end

lemma p_not_p_and (p q : pred' β)
: - (p ⋀ q) = -p ⋁ -q :=
begin
  apply pred_ext, intro x,
  simp [classical.not_and_iff_not_or_not],
end

lemma p_not_p_or (p q : pred' β)
: - (p ⋁ q) = -p ⋀ -q :=
begin
  apply pred_ext, intro x,
  simp [not_or_iff_not_and_not],
end

lemma p_not_and_self_or (p q : pred' β) :
- p ⋀ (p ⋁ q) = -p ⋀ q :=
by rw [p_and_over_or_left,p_not_and_self,False_p_or]

@[simp]
lemma p_exists_to_fun {t : Sort u'} (P : t → pred' β) (i : β)
: (∃∃ x, P x) i ↔ (∃ x, P x i) :=
by refl

@[simp]
lemma p_forall_to_fun {t : Sort u'} (P : t → pred' β) (i : β)
: (∀∀ x, P x) i ↔ (∀ x, P x i) :=
by refl

lemma ew_p_forall {t} (p : t → pred' β)
: ⦃ ∀∀ x, p x ⦄ ↔ ∀ x, ⦃ p x ⦄ :=
begin
  simp [ew,p_forall],
  rw [forall_swap], refl
end

lemma p_not_p_exists {t : Sort*} (p : t → pred' β) :
(- ∃∃ x, p x) = (∀∀ x, -p x) :=
by lifted_pred [not_exists_iff_forall_not,p_exists]

lemma p_exists_p_imp {t} (p : t → pred' β) (q : pred' β) :
(∃∃ x, p x) ⟶ q = (∀∀ x, p x ⟶ q) :=
begin
  apply pred_ext, intro,
  simp,
end

lemma p_or_comm (p q : pred' β) : p ⋁ q = q ⋁ p :=
begin apply pred_ext, intro x, simp end

lemma p_or_assoc (p q r : pred' β) : p ⋁ (q ⋁ r) = p ⋁ q ⋁ r :=
begin apply pred_ext, intro x, simp end

instance p_or_is_assoc : is_associative (pred' β) (⋁) :=
⟨ by { intros, rw p_or_assoc, } ⟩
instance p_or_is_comm : is_commutative (pred' β) (⋁) :=
⟨ by apply p_or_comm ⟩

lemma p_and_comm (p q : pred' β) : p ⋀ q = q ⋀ p :=
begin apply pred_ext, intro x, simp end

lemma p_and_assoc (p q r : pred' β) : p ⋀ (q ⋀ r) = p ⋀ q ⋀ r :=
begin apply pred_ext, intro x, simp end

instance p_and_is_assoc : is_associative (pred' β) (⋀) :=
⟨ by { intros, rw p_and_assoc, } ⟩
instance p_and_is_comm : is_commutative (pred' β) (⋀) :=
⟨ by apply p_and_comm ⟩

lemma p_and_p_imp (p q r : pred' β) : p ⋀ q ⟶ r = p ⟶ (q ⟶ r) :=
by lifted_pred

@[simp]
lemma p_or_intro_left (p q : pred' β)
: p ⟹ p ⋁ q :=
assume _, or.intro_left _

@[simp]
lemma p_or_intro_right (p q : pred' β)
: q ⟹ p ⋁ q :=
assume _, or.intro_right _

lemma p_or_entails_of_entails {p q r : pred' β}
  (h₀ : p ⟹ r)
  (h₁ : q ⟹ r)
: p ⋁ q ⟹ r :=
assume _, or.rec (h₀ _) (h₁ _)

lemma entails_p_or_of_entails_left {p q r : pred' β}
  (h₀ : p ⟹ q)
: p ⟹ q ⋁ r :=
assume x, (or.intro_left _) ∘ (h₀ x)

lemma entails_p_or_of_entails_right {p q r : pred' β}
  (h₀ : p ⟹ r)
: p ⟹ q ⋁ r :=
assume x, (or.intro_right _) ∘ (h₀ x)

lemma entails_p_and_of_entails {p q r : pred' β}
  (h₀ : p ⟹ q)
  (h₁ : p ⟹ r)
: p ⟹ q ⋀ r :=
assume x Hp, ⟨h₀ _ Hp,h₁ _ Hp⟩

lemma p_and_entails_of_entails_left {p q r : pred' β}
  (h₁ : p ⟹ r)
: p ⋀ q ⟹ r :=
assume x Hp, h₁ _ Hp.left

lemma p_and_entails_of_entails_right {p q r : pred' β}
  (h₁ : q ⟹ r)
: p ⋀ q ⟹ r :=
assume x Hp, h₁ _ Hp.right

@[simp]
lemma p_and_elim_left (p q : pred' β)
: p ⋀ q ⟹ p :=
assume x, and.left

@[simp]
lemma p_and_elim_right (p q : pred' β)
: p ⋀ q ⟹ q :=
assume x, and.right

@[trans]
lemma entails_trans {p q r : pred' β}
  (h₀ : p ⟹ q)
  (h₁ : q ⟹ r)
: p ⟹ r :=
assume x, h₁ x ∘ h₀ x

lemma p_not_comp (p : pred' α) (f : β → α)
: -(p '∘ f) = -p '∘ f :=
by lifted_pred

lemma comp_entails_comp {p q : pred' β} (f : α → β)
  (H : p ⟹ q)
: p '∘ f ⟹ q '∘ f :=
begin
  intros x h, simp at ⊢ h,
  apply H _ h
end

@[monotonic]
lemma p_and_entails_p_and_left (p q x : pred' β)
  (h : p ⟹ q)
: p ⋀ x ⟹ q ⋀ x :=
assume x, and.imp_left (h x)

@[monotonic]
lemma p_and_entails_p_and_right {p q : pred' β} (x : pred' β)
  (h : p ⟹ q)
: x ⋀ p ⟹ x ⋀ q :=
assume x, and.imp_right (h x)

@[monotonic]
lemma p_not_entails_p_not_right {p q : pred' β}
  (h : q ⟹ p)
: - p ⟹ - q :=
assume x, mt (h x)

lemma entails_of_eq (p q : pred' β)
  (h : p = q)
: p ⟹ q :=
by simp [h]

lemma p_and_entails_p_or (p q : pred' β)
: p ⋀ q ⟹ p ⋁ q :=
assume x, or.intro_left _ ∘ and.left

lemma True_p_imp (p : pred' β)
: True ⟶ p = p :=
by lifted_pred

lemma ew_eq_true {p : pred' β} : ⦃ p ⦄ → p = True :=
begin
  unfold ew, intros h,
  lifted_pred [h],
end

@[monotonic]
lemma ew_imp_ew {p q : pred' β}
  (H : p ⟹ q)
: ⦃ p ⦄ → ⦃ q ⦄ :=
forall_imp_forall H

lemma entails_of_pointwise {p q : pred' β}
  (h : ∀ i, p i → q i)
: p ⟹ q := h

lemma entails_to_pointwise {p q : pred' β}
  (h : p ⟹ q)
: ∀ i, p i → q i := h

lemma ew_str {p : pred' β}
: ⦃ p ⦄ → ∀ x, p x :=
id

lemma ew_wk {p : pred' β}
: (∀ x, p x) → ⦃ p ⦄ :=
id

lemma entails_of_forall_impl {p q : pred' β}
  (h : p ⟹ q)
: ∀ i, (p ⟶ q) i := h

lemma impl_of_p_impl {p q : pred' β} (i : β)
  (h : (p ⟶ q) i)
: p i → q i := h


open interactive.types interactive
open lean.parser lean tactic (hiding funext)
meta def entails_or_ew {α : Type u} (t : expr) (tag : string)
   (ent_tac ew_tac : tactic α) : tactic α :=
do match t with
    | `(_ ⟹ _) := ent_tac
    | `(ew _) := ew_tac
    | _ := fail format!"expecting {tag} of shape `_ ⟹ _` or `⦃ _ ⦄`"
   end

meta def pointwise (h : parse (many ident)) (ids : parse with_ident_list) : tactic unit :=
do ls ← mmap get_local h,
   t ← target,
   entails_or_ew t "goal" `[refine entails_of_pointwise _] `[refine ew_wk _],
   tactic.intro_lst ids,
   mmap' (λ l : expr,
    do entails_or_ew t "goal" (to_expr ``(entails_to_pointwise %%l))
                              (to_expr ``(ew_str %%l))
           >>= note l.local_pp_name none,
       try (clear l)) ls

run_cmd add_interactive [`pointwise]

lemma p_or_over_p_exists_left {t} (p : t → pred' β) (q : pred' β) {w : t → pred' β}
  (h : ⦃ ∃∃ x : t, w x ⦄)
: q ⋁ (∃∃ x, p x) = (∃∃ x, q ⋁ p x) :=
begin
  lifted_pred,
  have _inst : nonempty t := nonempty_of_exists (h x),
  simp [distrib_or_over_exists_left,p_exists,pred.p_exists],
end

@[congr]
lemma {v} p_exists_congr {α : Sort u} {β : Sort v} {p q : α → pred' β}
  (h : ∀ i, p i = q i)
: pred.p_exists p = pred.p_exists q :=
begin
  change p_exists p = p_exists q,
  lifted_pred,
  rw [exists_congr],
  intro, rw h,
end

lemma p_and_over_p_exists_right {t} (p : t → pred' β) (q : pred' β)
: (∃∃ x, p x) ⋀ q = (∃∃ x, p x ⋀ q) :=
begin
  apply pred_ext, intro i,
  simp,
end

lemma p_and_over_p_exists_left {t} (p : pred' β) (q : t → pred' β)
: p ⋀ (∃∃ x, q x) = (∃∃ x, p ⋀ q x) :=
begin
  rw [p_and_comm,p_and_over_p_exists_right],
  apply p_exists_congr,
  intro, simp [p_and_comm]
end

lemma shunting {β : Sort*} (p q r : pred' β)
: p ⟶ q ⋁ r = (p ⋀ - q) ⟶ r :=
begin
  lifted_pred,
  begin [smt] by_cases r x, by_cases q x end,
end

lemma shunting' {β : Sort*} (p q r : pred' β)
: p ⟶ (q ⟶ r) = (p ⋀ q) ⟶ r :=
by lifted_pred

lemma imp_swap {β : Sort*} (p q r : pred' β)
: p ⟶ (q ⟶ r) = q ⟶ (p ⟶ r) :=
by { lifted_pred,
     begin [smt] split, intros, by_cases (r x) end }

lemma entails_swap {β : Sort*} (p q r : pred' β)
: p ⟹ (q ⟶ r) ↔ q ⟹ (p ⟶ r) :=
by simp [p_entails,imp_swap]
-- ◻◇p ⊢ ◻◇q τ
-- `τ : stream σ, h : (◻◇p) τ ⊢ (◻◇q) τ`
lemma p_not_p_imp {β : Sort*} (p q : pred' β)
: (-p) ⟶ q = p ⋁ q :=
by rw [← True_p_and (-p),← shunting,True_p_imp]

lemma p_or_entails_p_or {p p' q q' : pred' β}
  (H₀ : p  ⟹ q )
  (H₁ : p' ⟹ q')
: p ⋁ p' ⟹ q ⋁ q' :=
assume i, or.imp (H₀ _) (H₁ _)

@[monotonic]
lemma p_or_entails_p_or_left (p q x : pred' β)
: p ⟹ q → p ⋁ x ⟹ q ⋁ x :=
begin
  intros h i, simp,
  apply or.imp_left (h _),
end


lemma p_or_not_and {β : Sort*} (p q : pred' β)
: p ⋁ (- p ⋀ q) = p ⋁ q :=
begin
  lifted_pred,
  rw [← or_not_and (p _) (q _)],
  simp
end

lemma p_exists_intro {t : Sort u'} {p : t → pred' β} (x : t)
: p x ⟹ (∃∃ x, p x) :=
assume s h, ⟨x,h⟩

lemma p_exists_elim {t : Sort u'} {p : t → pred' β} {q : pred' β}
  (H : ∀ x, p x ⟹ q)
: (∃∃ x, p x) ⟹ q :=
assume s h, exists.elim h (λ x, H x s)

lemma p_exists_entails_p_exists {t : Sort u'} (p q : t → pred' β)
: (∀ x, p x ⟹ q x) → (∃∃ x, p x) ⟹ (∃∃ x, q x) :=
begin
  intros h i,
  simp [- exists_imp_distrib],
  apply exists_imp_exists,
  intro,
  apply h
end

lemma p_exists_over_p_or {t} (p q : t → pred' β)
: (∃∃ x, p x) ⋁ (∃∃ x, q x) = (∃∃ x, p x ⋁ q x) :=
begin
  apply mutual_entails,
  apply p_or_entails_of_entails,
  { refine p_exists_entails_p_exists p _ _,
    intro, apply p_or_intro_left },
  { apply p_exists_entails_p_exists,
    intro, apply p_or_intro_right },
  { refine p_exists_elim _,
    intro,
    apply p_or_entails_of_entails,
    { apply entails_p_or_of_entails_left,
      apply p_exists_intro, },
    { apply entails_p_or_of_entails_right,
      apply p_exists_intro, }, }
end


lemma p_exists_entails_p_exists' {t : Sort u₀} {t' : Sort u₁}
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
by lifted_pred

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
  lifted_pred,
  unfold p_entails at Hf Hg,
  rw [← ew_p_forall] at Hf Hg,
  rw exists_variable_change _ _ f g,
  apply Hf,
  apply Hg,
end

lemma p_exists_range_subtype {α : Sort u}
  (p : α → Prop) (q : α → pred' β)
: (∃∃ i, p i ⋀ q i : pred' β) = (∃∃ j : subtype p, q (j.val)) :=
begin
  lifted_pred,
  rw [← exists_range_subtype],
end

lemma p_or_iff_not_imp (p q : pred' β)
: p ⋁ q = - p ⟶ q :=
begin
  lifted_pred,
  simp [or_iff_not_imp],
end

lemma p_forall_fin_zero (p : fin 0 → pred' β)
: (∀∀ i, p i) = True :=
begin
  lifted_pred,
  simp [forall_fin_zero_iff_true],
end

lemma p_forall_split_one {n : ℕ} (p : fin (nat.succ n) → pred' β)
: (∀∀ i, p i) = p fin.max ⋀ (∀∀ i, restr p i) :=
begin
  lifted_pred,
  simp [forall_split_one],
  refl,
end

lemma p_exists_split_one {n : ℕ} (p : fin (nat.succ n) → pred' β)
: (∃∃ i, p i) = p fin.max ⋁ (∃∃ i, restr p i) :=
begin
  lifted_pred,
  simp [exists_split_one],
  refl,
end

instance entails_category {α} : category (@p_entails α) :=
  { ident := by { intro, refl }
  , comp  := by { intros _ _ _, exact flip entails_trans }
  , assoc := by { intros, refl }
  , left_ident  := by { intros, refl }
  , right_ident := by { intros, refl } }

attribute [irreducible] p_not p_entails ew
-- attribute [trans]  entails_trans

end predicate

-- TODO:
--   * switch definition of pred' to a record to strengthen encapsulation
--   * use τ ⊧ []φ instead of ([]φ) τ
