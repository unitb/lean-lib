
import util.logic
import util.data.fin
import util.category
import util.meta.tactic.basic
import util.meta.tactic.monotonicity

run_cmd mk_simp_attr `predicate

namespace predicate

universe variables u u' u₀ u₁ u₂

variables {α : Sort u₀}
variables {β : Sort u₁}
variables {γ : Sort u₂}

-- @[reducible]
structure pred' (α : Sort u) : Type u :=
  (apply : α → Prop)

notation x ` ⊨ `:53 y:52 := y.apply x

structure judgement (h y : pred' α) : Prop :=
(apply : ∀ σ, σ ⊨ h → σ ⊨ y)

infix ` ⊢ `:53 := judgement

def contramap : pred' α → (β → α) → pred' β
 | ⟨ p ⟩ f := ⟨ p ∘ f ⟩

infixr ` '∘ `:90 := contramap

@[simp, predicate]
lemma contramap_apply (p : pred' α) (f : β → α) (x : β)
: x ⊨ (p '∘ f) = f x ⊨ p :=
by { cases p , refl }

def lifted₀ (p : Prop) : pred' α := ⟨ λ _, p ⟩
def lifted₁ (op : Prop → Prop) (p : pred' α) : pred' α :=
⟨ λ i, op (i ⊨ p) ⟩
def lifted₂ (op : Prop → Prop → Prop) (p q : pred' α) : pred' α :=
⟨ λ i, op (i ⊨ p) (i ⊨ q) ⟩

-- def ew (p : pred' α) : Prop :=
-- ∀ i, i ⊨ p

def False {α} : pred' α := lifted₀ false
def True {α} : pred' α := lifted₀ true
@[reducible]
def holds (x : pred' α) := ∀ Γ, judgement Γ x

prefix `⊩ `:53  := holds

def p_or (p₀ p₁ : pred' α) : pred' α :=
lifted₂ or p₀ p₁

@[simp, predicate]
lemma p_or_to_fun (p₀ p₁ : pred' α) (x : α)
: x ⊨ p_or p₀ p₁ ↔ x ⊨ p₀ ∨ x ⊨ p₁ := by refl

def p_and (p₀ p₁ : pred' α) : pred' α :=
lifted₂ and p₀ p₁

@[simp, predicate]
lemma p_and_to_fun (p₀ p₁ : pred' α) (x : α)
: x ⊨ p_and p₀ p₁ ↔ x ⊨ p₀ ∧ x ⊨ p₁ := by refl

def p_impl (p₀ p₁ : pred' α) : pred' α :=
lifted₂ implies p₀ p₁

def p_equiv (p₀ p₁ : pred' α) : pred' α :=
lifted₂ (↔) p₀ p₁

@[simp, predicate]
lemma p_impl_to_fun (p₀ p₁ : pred' α) (x : α)
: x ⊨ p_impl p₀ p₁ ↔ (x ⊨ p₀ → x ⊨ p₁) := by refl

@[simp, predicate]
lemma p_equiv_to_fun (p₀ p₁ : pred' α) (x : α)
: x ⊨ p_equiv p₀ p₁ ↔ (x ⊨ p₀ ↔ x ⊨ p₁) := by refl

lemma p_impl_revert {Γ p q : pred' α}
  (h : Γ ⊢ p_impl p q)
: Γ ⊢ p → Γ ⊢ q :=
begin
  intros h₁,
  constructor, introv h₂,
  apply h.apply _ h₂,
  apply h₁.apply _ h₂,
end

instance imp_to_fun ⦃α⦄ ⦃Γ p q : pred' α⦄ : has_coe_to_fun (Γ ⊢ p_impl p q) :=
{ F := λ _,(Γ ⊢ p) → (Γ ⊢ q)
, coe := p_impl_revert }

def p_entails (p₀ p₁ : pred' α) : Prop :=
⊩ p_impl p₀ p₁

lemma p_entails_of_fun (p₀ p₁ : pred' α) (x : β)
: p_entails p₀ p₁ ↔ ∀ Γ, Γ ⊢ p₀ → Γ ⊢ p₁ :=
begin
  split ; intros h _,
  { intro h', apply h Γ h' },
  { constructor,
    introv h₀ h₁,
    apply (h  ⟨ eq σ ⟩ _).apply σ rfl,
    constructor, introv h,
    cases h, assumption, }
end

def p_not (p : pred' α) : pred' α :=
lifted₁ not p

@[simp]
lemma False_eq_false (Γ : pred' β) : Γ ⊢ False ↔ Γ = False :=
begin
  split ; intro h,
  { cases h with h, cases Γ with Γ, simp [False,lifted₀],
    congr, funext σ,
    specialize h σ, apply eq_false_intro,
    intro h',
    apply h h' },
  { rw h, constructor,
    intro, exact id }
end

@[simp, predicate]
lemma False_sem (σ : β) : σ ⊨ False ↔ false :=
by simp [False,lifted₀]

@[simp]
lemma True_eq_true (Γ : pred' β) : Γ ⊢ True = true :=
by { apply eq_true_intro, constructor, intros, trivial }
@[simp]
lemma True_holds : ⊩ @True β :=
by simp [holds]

@[simp, predicate]
lemma True_sem (σ : β) : σ ⊨ True ↔ true :=
by simp [holds]

def pred.p_exists {β : Sort u'} {t : Sort u} (P : t → pred' β) : pred' β :=
⟨λ x, ∃ y, x ⊨ P y⟩

class has_p_exists (α : Sort u) (β : Sort u') :=
  (p_exists : (β → α) → α)

instance pred_has_p_exists {α : Sort u} {β : Sort u'} : has_p_exists (pred' α) β :=
⟨ @pred.p_exists _ _ ⟩

export has_p_exists (p_exists)

def p_forall {t : Sort u} {β : Sort u'} (P : t → pred' β) : pred' β :=
⟨ λ x, ∀ y, x ⊨ P y ⟩

notation `∃∃` binders `, ` r:(scoped P, p_exists P) := r
notation `∀∀` binders `, ` r:(scoped P, p_forall P) := r

lemma p_forall_revert {Γ} {p : β → pred' α}
  (h : Γ ⊢ p_forall p)
: Π i, Γ ⊢ p i :=
begin
  introv,
  constructor, introv h₂,
  apply h.apply _ h₂,
end

instance forall_to_fun {Γ : pred' α} ⦃p : β → pred' α⦄ : has_coe_to_fun (Γ ⊢ p_forall p) :=
{ F := λ _, Π i, (Γ ⊢ p i)
, coe := p_forall_revert }

instance : has_coe Prop (pred' α) :=
⟨ lifted₀ ⟩

instance proof_coe (p : Prop) (Γ : pred' α) : has_coe p (Γ ⊢ p) :=
⟨ assume h, ⟨ λ x _, h ⟩ ⟩

instance to_prop_to_pred : has_coe (α → Prop) (pred' α) :=
⟨ pred'.mk ⟩

@[simp, predicate]
lemma coe_apply (p : Prop) (x : β)
: x ⊨ (p : pred' β) ↔ p :=
by { unfold_coes, simp [lifted₀,pred'.apply] }

infixl ` ⋁ `:65 := p_or
infixl ` ⋀ `:70 := p_and
infixr ` ⟶ `:60 := p_impl
precedence ≡:55
infixr ` ≡ ` := p_equiv
infix ` ⟹ `:60 := p_entails
-- notation `⦃ `:max act ` ⦄`:0 := ew act
-- Γ ⊢ p
-- ∀ σ, σ ⊨ Γ → σ ⊨ p
instance : has_neg (pred' α) := has_neg.mk p_not

def ctx_impl (Γ p q : pred' α) : Prop :=
Γ ⊢ p ⟶ q

lemma p_imp_ext {Γ p q : pred' α}
  (h : ∀ σ, σ ⊨ Γ → σ ⊨ p → σ ⊨ q)
: Γ ⊢ p ⟶ q :=
⟨ h ⟩

lemma p_imp_sem {Γ p q : pred' α}
  (h : Γ ⊢ p ⟶ q)
: ∀ σ, σ ⊨ Γ → σ ⊨ p → σ ⊨ q :=
h.apply

@[simp]
lemma eq_judgement {p : pred' α} (σ : α)
: ↑(eq σ) ⊢ p ↔ σ ⊨ p :=
by { split ; intro h,
     { apply h.apply σ, exact rfl },
     { constructor, intros _ h', cases h', assumption } }

@[extensionality]
lemma pred_ext_sem {p q : pred' α}
  (h : ∀ σ, σ ⊨ p ↔ σ ⊨ q)
: p = q :=
begin
  cases p, cases q,
  congr, funext y,
  simp at h,
  rw h
end

lemma pred_ext {p q : pred' α}
  (h : ∀ Γ, Γ ⊢ p ↔ Γ ⊢ q)
: p = q :=
begin
  cases p, cases q,
  congr, funext y,
  specialize h (eq y),
  simp  at h,
  rw h,
end

lemma entails_of_pointwise {p q : pred' β}
  (h : ∀ σ, σ ⊨ p → σ ⊨ q)
: p ⟹ q :=
begin
  intros _, constructor, introv h',
  apply h,
end

lemma entails_of_forall_impl {p q : pred' β}
  (h : p ⟹ q)
: ∀ i, i ⊨ p ⟶ q :=
by { intros i hp, apply (h $ eq i).apply i rfl hp, }

lemma ew_str {p : pred' β}
: ⊩ p → ∀ x, x ⊨ p :=
by { intros h _, apply (h $ eq x).apply _ rfl }

lemma ew_wk {p : pred' β}
: (∀ x, x ⊨ p) → ⊩ p :=
by { intros h Γ, constructor,
     intros, apply h }

section
open interactive interactive.types lean lean.parser
     tactic tactic.interactive (simp)
local postfix `?`:9001 := optional
local postfix *:9001 := many
meta def using_idents := (tk "using" *> ident*) <|> pure []

meta def lifted_asm (v : expr) (h : name) : tactic unit :=
do h' ← get_local h,
   p ← to_expr ``(p_imp_sem  %%h' %%v)
     <|> to_expr ``(ew_str  %%h' %%v)
     <|> fail format!"assumtion {h} should be `⊩ p` or `p ⟹ q` or `Γ ⊢ p ⟶ q`",
   h ← note h none p,
   try $ simp ff [] [] (loc.ns [some h.local_pp_name]),
   try (clear h')

meta def lifted_pred (no_dflt : parse only_flag)
   (rs : parse simp_arg_list)
   (hs : parse using_idents) : tactic unit :=
do `[apply p_imp_ext _] <|> `[apply pred_ext_sem] <|> `[apply ew_wk _],
   v ← intro1,
   mmap' (lifted_asm v) (hs : list _),
   try (simp no_dflt rs [`predicate] (loc.ns [none])),
   try reflexivity
run_cmd add_interactive [`lifted_pred]
end

@[simp]
lemma p_and_comp (p q : pred' α) (f : β → α)
: ((p ⋀ q) '∘ f) = (p '∘ f) ⋀ (q '∘ f) :=
by lifted_pred

@[simp]
lemma coe_over_comp (p : α → Prop) (f : β → α)
: ((p : pred' α) '∘ f) = ↑(p ∘ f) :=
by lifted_pred

@[simp]
lemma p_or_comp (p q : pred' α) (f : β → α)
: ((p ⋁ q) '∘ f) = (p '∘ f) ⋁ (q '∘ f) :=
by lifted_pred

@[simp]
lemma p_exists_comp {t} (p : t → pred' α) (f : β → α)
: (p_exists p '∘ f) = (∃∃ x, p x '∘ f) :=
by lifted_pred [p_exists,pred.p_exists]

@[simp]
lemma coe_to_prop_p_and (p q : α → Prop)
: (λ s, p s ∧ q s : pred' α) = p ⋀ q := rfl

@[simp]
lemma coe_to_prop_p_or (p q : α → Prop)
: (λ s, p s ∨ q s : pred' α) = p ⋁ q := rfl

@[simp]
lemma coe_to_prop_p_not (p : α → Prop)
: (λ s, ¬ p s : pred' α) = - p := rfl

@[simp]
lemma coe_to_prop_p_equiv (p q : α → Prop)
: (λ s, p s ↔ q s : pred' α) = p ≡ q := rfl

lemma lifting_prop_asm (Γ : pred' α) {p : Prop} {q : pred' α}
  (h : p → Γ ⊢ q)
: Γ ⊢ p → Γ ⊢ q :=
begin
  intro h₁,
  constructor,
  introv h₂,
  have h₃ := h₁.apply _ h₂,
  apply (h h₃).apply _ h₂,
end

@[simp, predicate]
lemma p_not_to_fun (p₀ : pred' α) (x : α)
: x ⊨ (- p₀) ↔ ¬ x ⊨ p₀ := by { refl, }

lemma p_not_eq_not (p : pred' β) (x : β) : ¬ x ⊨ p ↔ x ⊨ (-p) :=
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
by lifted_pred

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
by lifted_pred

@[refl]
lemma ctx_impl_refl (Γ p : pred' β)
: ctx_impl Γ p p :=
by lifted_pred

@[refl]
lemma p_impl_refl (Γ p : pred' β)
: Γ ⊢ p ⟶ p :=
by lifted_pred

@[refl]
lemma equiv_refl (Γ p : pred' β)
: Γ ⊢ p ≡ p :=
by lifted_pred

lemma ctx_p_or_p_imp_p_or' {Γ p p' q q' : pred' α}
  (hp : ctx_impl Γ p p')
  (hq : ctx_impl Γ q q')
: ctx_impl Γ (p ⋁ q) (p' ⋁ q')  :=
by { lifted_pred using hp hq,
     begin [smt] intros, destruct a_1 end, }

lemma p_or_p_imp_p_or' {p p' q q' : pred' α}
  (hp : p ⟹ p')
  (hq : q ⟹ q')
: (p ⋁ q)  ⟹  (p' ⋁ q')  :=
by { lifted_pred using hp hq,
     apply or.imp hp hq, }

lemma p_or_p_imp_p_or {p p' q q' : pred' α} {τ}
  (hp : τ ⊨ p ⟶ p')
  (hq : τ ⊨ q ⟶ q')
: τ ⊨ p ⋁ q → τ ⊨ p' ⋁ q' :=
by apply or.imp hp hq

@[monotonic]
lemma ctx_p_and_p_imp_p_and_right' {Γ p q q' : pred' α}
  (hq : ctx_impl Γ q q')
: ctx_impl Γ ( p ⋀ q ) ( p ⋀ q' ) :=
by { lifted_pred using hq, intros,
     split ; auto, }

@[monotonic]
lemma p_and_p_imp_p_and_right' {p q q' : pred' α}
  (hq : q ⟹ q')
: ( p ⋀ q ) ⟹ ( p ⋀ q' ) :=
assume _, ctx_p_and_p_imp_p_and_right' (hq _)

@[monotonic]
lemma ctx_p_or_p_imp_p_or_right {Γ p q q' : pred' α}
  (hq : ctx_impl Γ q q')
: ctx_impl Γ ( p ⋁ q ) ( p ⋁ q' ) :=
by { apply ctx_p_or_p_imp_p_or' _ hq, refl }

@[monotonic]
lemma p_or_p_imp_p_or_right' {p q q' : pred' α}
  (hq : q ⟹ q')
: ( p ⋁ q ) ⟹ ( p ⋁ q' ) :=
by { apply p_or_p_imp_p_or' _ hq, refl }

lemma p_or_p_imp_p_or_right {p q q' : pred' α} {τ}
  (hq : τ ⊨ q ⟶ q')
: τ ⊨ p ⋁ q → τ ⊨ p ⋁ q' :=
by apply or.imp id hq

lemma p_or_p_imp_p_or_left {p p' q : pred' α} {τ}
  (hp : τ ⊨ p ⟶ p')
: τ ⊨ p ⋁ q → τ ⊨ p' ⋁ q :=
by apply or.imp hp id

lemma p_imp_p_imp_p_imp {p p' q q' : pred' α} {τ}
  (hp : τ ⊨ p' ⟶ p)
  (hq : τ ⊨ q ⟶ q')
: τ ⊨ p ⟶ q → τ ⊨ p' ⟶ q' :=
assume hpq, hq ∘ hpq ∘ hp

lemma revert_p_imp {p q : pred' α}
  (h : ⊩ p ⟶ q)
: p ⊢ q :=
begin
  constructor, intro,
  exact (h True).apply σ trivial,
end

lemma revert_p_imp' {p q r : pred' α}
  (h : p ⟹ q)
: q ⊢ r → p ⊢ r :=
by { intro h₀, constructor,
     introv h₁, apply h₀.apply,
     apply (h p).apply _ h₁ h₁, }

@[simp]
lemma from_True {p : pred' α}
: True ⊢ p ↔ ⊩ p :=
by { unfold holds ; split ; intro h,
     intro, apply revert_p_imp' _ h, simp,
     apply h }

lemma intro_p_imp {p q : pred' α}
  (h : p ⊢ q)
: ⊩ p ⟶ q :=
begin
  intro, constructor, introv h',
  apply h.apply,
end

lemma p_imp_entails_p_imp {p p' q q' : pred' α}
  (hp : p' ⟹ p)
  (hq : q ⟹ q')
: ( p ⟶ q ) ⟹ ( p' ⟶ q' ) :=
by { lifted_pred using hp hq, intros,
     repeat { xassumption }, }

lemma p_imp_p_imp_p_imp_left {p p' q : pred' α} {τ}
  (hp : τ ⊨ p' ⟶ p)
: τ ⊨ p ⟶ q → τ ⊨ p' ⟶ q :=
p_imp_p_imp_p_imp hp id

lemma p_imp_p_imp_p_imp_right {p q q' : pred' α} {τ}
  (hq : τ ⊨ q ⟶ q')
: τ ⊨ p ⟶ q → τ ⊨ p ⟶ q' :=
p_imp_p_imp_p_imp id hq


@[monotonic]
lemma ctx_imp_entails_p_imp_left {Γ p p' q : pred' α}
  (hp : ctx_impl Γ p' p)
: ctx_impl Γ ( p ⟶ q ) ( p' ⟶ q ) :=
by { lifted_pred using hp, intros, auto }

@[monotonic]
lemma p_imp_entails_p_imp_left {p p' q : pred' α}
  (hp : p' ⟹ p)
: ( p ⟶ q ) ⟹ ( p' ⟶ q ) :=
p_imp_entails_p_imp hp (by refl)

lemma entails_imp_entails_left {p p' q : pred' α}
  (hp : p' ⟹ p)
: ( p ⟹ q ) → ( p' ⟹ q ) :=
begin
  intros h₁ Γ, constructor,
  introv h₂ h₃,
  apply (h₁ Γ).apply _ h₂,
  apply (hp Γ).apply _ h₂ h₃,
end

@[monotonic]
lemma ctx_p_imp_entails_p_imp_right {Γ p q q' : pred' α}
  (hq : ctx_impl Γ q q')
: ctx_impl Γ ( p ⟶ q ) ( p ⟶ q' ) :=
by { lifted_pred using hq, intros, auto }

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
  lifted_pred, split,
  { begin [smt] intros, eblast end },
  { begin [smt] intros, destruct a end },
end

lemma p_and_over_or_right (p q r : pred' β)
: (q ⋁ r) ⋀ p = (q ⋀ p) ⋁ (r ⋀ p) :=
begin
  lifted_pred, split,
  { begin [smt] intros, eblast end },
  { begin [smt] intros, destruct a end },
end

instance : is_left_distrib (pred' β) (⋀) (⋁) :=
⟨ p_and_over_or_left ⟩
instance : is_right_distrib (pred' β) (⋀) (⋁) :=
⟨ by { intros, apply p_and_over_or_right } ⟩
instance : is_left_id (pred' β) (⋀) True :=
⟨ by simp ⟩
instance : is_right_id (pred' β) (⋀) True :=
⟨ by simp ⟩
instance or_left_id : is_left_id (pred' β) (⋁) False :=
⟨ by simp ⟩
instance or_right_id : is_right_id (pred' β) (⋁) False :=
⟨ by simp ⟩

lemma p_or_over_and_left (p q r : pred' β)
: p ⋁ (q ⋀ r) = (p ⋁ q) ⋀ (p ⋁ r) :=
begin
  lifted_pred, split,
  { begin [smt] intros, destruct a end },
  { begin [smt] intros, destruct a.left, end },
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
  lifted_pred using h₀ h₁,
  split ; assumption,
end

@[simp]
lemma False_entails (p : pred' β)
: False ⟹ p :=
by lifted_pred

@[simp]
lemma p_imp_False (p : pred' β)
: p ⟶ False = -p :=
by lifted_pred

lemma p_and_p_not_self (p : pred' β)
: p ⋀ -p = False :=
by lifted_pred

@[simp]
lemma p_or_p_not_self (p : pred' β)
: p ⋁ -p = True :=
by lifted_pred [classical.em]

lemma em (p : pred' β)
: ⊩ p ⋁ -p :=
by lifted_pred [classical.em]

lemma p_and_p_or_p_not_self (p q : pred' β)
: p ⋀ (q ⋁ -p) = p ⋀ q :=
by simp [p_and_over_or_left,p_and_p_not_self]

lemma p_not_and_self (p : pred' β)
: (-p) ⋀ p = False :=
by lifted_pred

lemma p_not_p_and (p q : pred' β)
: - (p ⋀ q) = -p ⋁ -q :=
by lifted_pred [classical.not_and_iff_not_or_not]

lemma p_not_p_or (p q : pred' β)
: - (p ⋁ q) = -p ⋀ -q :=
by lifted_pred [not_or_iff_not_and_not]

lemma p_not_and_self_or (p q : pred' β) :
- p ⋀ (p ⋁ q) = -p ⋀ q :=
by rw [p_and_over_or_left,p_not_and_self,False_p_or]

@[simp, predicate]
lemma p_exists_apply {t : Sort u'} {P : t → pred' β} (σ : β)
: σ ⊨ (∃∃ x, P x) ↔ (∃ x, σ ⊨ P x) :=
by { unfold p_exists pred.p_exists }

lemma p_exists_to_fun {t : Sort u'} {h : pred' β} {P : t → pred' β}
  (x : t)
  (Hh : h ⊢ P x)
: h ⊢ (∃∃ x, P x) :=
by { constructor, intros _ h', existsi x,
     apply Hh.apply _ h', }

@[simp, predicate]
lemma models_p_forall {t : Sort u'} (P : t → pred' β) (σ : β)
: σ ⊨ (∀∀ x, P x) ↔ (∀ x, σ ⊨ P x) := by refl

lemma p_forall_to_fun {t : Sort u'} (h : pred' β) (P : t → pred' β)
: h ⊢ (∀∀ x, P x) ↔ (∀ x, h ⊢ P x) :=
begin
  split ; intro h,
  { intro, constructor, intros,
    cases h with h,
    apply h σ a, },
  { constructor,
    introv h' x,
    apply (h x).apply _ h', }
end

lemma p_forall_subtype_to_fun {t : Sort u'} (h : pred' β) (p : t → Prop) (q : t → pred' β)
: h ⊢ (∀∀ x, p x ⟶ q x) ↔ (∀ x, p x → h ⊢ q x) :=
begin
  split,
  { intros h x hp, apply h x hp },
  { intros h,
    constructor,
    introv hσ x hp,
    apply (h x hp).apply _ hσ, }
end

lemma ew_p_forall {t} (p : t → pred' β)
: ⊩ (∀∀ x, p x) ↔ ∀ x, ⊩ p x :=
by { simp only [holds,forall_swap] { single_pass := tt },
     apply forall_congr, intro,
     apply p_forall_to_fun }

lemma p_not_p_exists {t : Sort*} (p : t → pred' β) :
(- ∃∃ x, p x) = (∀∀ x, -p x) :=
by lifted_pred [not_exists_iff_forall_not,p_exists,pred.p_exists]

lemma p_exists_p_imp {t} (p : t → pred' β) (q : pred' β)
: (∃∃ x, p x) ⟶ q = (∀∀ x, p x ⟶ q) :=
by lifted_pred [p_exists,pred.p_exists]

lemma p_or_comm (p q : pred' β) : p ⋁ q = q ⋁ p :=
by lifted_pred

lemma p_or_assoc (p q r : pred' β) : p ⋁ (q ⋁ r) = p ⋁ q ⋁ r :=
by lifted_pred

instance p_or_is_assoc : is_associative (pred' β) (⋁) :=
⟨ by { intros, rw p_or_assoc, } ⟩
instance p_or_is_comm : is_commutative (pred' β) (⋁) :=
⟨ by apply p_or_comm ⟩

lemma p_and_comm (p q : pred' β) : p ⋀ q = q ⋀ p :=
by lifted_pred

lemma p_and_assoc (p q r : pred' β) : p ⋀ (q ⋀ r) = p ⋀ q ⋀ r :=
by lifted_pred

instance p_and_is_assoc : is_associative (pred' β) (⋀) :=
⟨ by { intros, rw p_and_assoc, } ⟩
instance p_and_is_comm : is_commutative (pred' β) (⋀) :=
⟨ by apply p_and_comm ⟩

@[simp]
lemma p_and_p_imp (p q r : pred' β) : p ⋀ q ⟶ r = p ⟶ (q ⟶ r) :=
by lifted_pred

-- lemma p_imp_intro_wrong (Γ p q : pred' β)
--   (h : Γ ⊢ p → Γ ⊢ q)
-- : Γ ⊢ p ⟶ q :=
-- sorry

lemma p_imp_intro (p q r : pred' β)
  (h : ∀ Γ, Γ ⊢ p → Γ ⊢ q → Γ ⊢ r)
  (Γ : pred' β)
  (h' : Γ ⊢ p)
: Γ ⊢ q ⟶ r :=
begin
  constructor, introv hΓ hq,
  apply (h (eq σ) _ _).apply _ rfl ;
  constructor
  ; intros _ h
  ; cases h,
  { apply h'.apply _ hΓ },
  assumption
end

@[simp]
lemma p_or_intro_left (p q : pred' β)
: p ⟹ p ⋁ q :=
by { lifted_pred,
     begin [smt] intros end }

@[simp]
lemma p_or_intro_right (p q : pred' β)
: q ⟹ p ⋁ q :=
by { lifted_pred,
     begin [smt] intros end }

@[simp]
lemma p_and_intro (p q : pred' β)
: p ⟹ (q ⟶ p ⋀ q) :=
by { lifted_pred,
     begin [smt] intros end }

lemma p_or_entails_of_entails' {Γ p q r : pred' β}
  (h₀ : Γ ⊢ p ⟶ r)
  (h₁ : Γ ⊢ q ⟶ r)
: Γ ⊢ p ⋁ q ⟶ r :=
by { constructor, simp_intros _ hΓ _,
     have h₀ := h₀.apply σ hΓ, simp at h₀,
     have h₁ := h₁.apply σ hΓ, simp at h₁,
     begin [smt] intros, destruct a, end }

lemma p_or_entails_of_entails {p q r : pred' β}
  (h₀ : p ⟹ r)
  (h₁ : q ⟹ r)
: p ⋁ q ⟹ r :=
by { lifted_pred using h₀ h₁,
     begin [smt] intros, destruct a end }

lemma entails_p_or_of_entails_left {p q r : pred' β}
  (h₀ : p ⟹ q)
: p ⟹ q ⋁ r :=
by { lifted_pred using h₀,
     begin [smt] intros end }

lemma entails_p_or_of_entails_right {p q r : pred' β}
  (h₀ : p ⟹ r)
: p ⟹ q ⋁ r :=
by { lifted_pred using h₀,
     begin [smt] intros end }

lemma entails_p_and_of_entails {p q r : pred' β}
  (h₀ : p ⟹ q)
  (h₁ : p ⟹ r)
: p ⟹ q ⋀ r :=
by { lifted_pred using h₀ h₁,
     begin [smt] intros end }

lemma p_and_entails_of_entails_left {p q r : pred' β}
  (h₁ : p ⟹ r)
: p ⋀ q ⟹ r :=
by { lifted_pred using h₁,
     begin [smt] intros end }

lemma p_and_entails_of_entails_right {p q r : pred' β}
  (h₁ : q ⟹ r)
: p ⋀ q ⟹ r :=
by { lifted_pred using h₁,
     begin [smt] intros end }

@[simp]
lemma p_and_elim_left (p q : pred' β)
: p ⋀ q ⟹ p :=
by { lifted_pred,
     begin [smt] intros end }

@[simp]
lemma p_and_elim_right (p q : pred' β)
: p ⋀ q ⟹ q :=
by lifted_pred

lemma judgement.left {Γ p q : pred' β}
  (h : Γ ⊢ p ⋀ q)
: Γ ⊢ p :=
p_and_elim_left p q Γ h

lemma judgement.right {Γ p q : pred' β}
  (h : Γ ⊢ p ⋀ q)
: Γ ⊢ q :=
p_and_elim_right p q Γ h

lemma p_imp_trans {Γ p q r : pred' β}
  (h₀ : Γ ⊢ p ⟶ q)
  (h₁ : Γ ⊢ q ⟶ r)
: Γ ⊢ p ⟶ r :=
begin
  lifted_pred using h₀ h₁,
  intros,
  auto,
end

@[trans]
lemma entails_trans {p q r : pred' β}
  (h₀ : p ⟹ q)
  (h₁ : q ⟹ r)
: p ⟹ r :=
begin
  lifted_pred using h₀ h₁,
  intro, auto,
end

@[simp]
lemma p_not_comp (p : pred' α) (f : β → α)
: -p '∘ f = -(p '∘ f) :=
by lifted_pred

lemma comp_entails_comp {p q : pred' β} (f : α → β)
  (H : p ⟹ q)
: p '∘ f ⟹ q '∘ f :=
begin
  intros Γ, constructor,
  introv h hp,
  simp at ⊢ hp,
  apply (H (eq $ f σ)).apply (f σ) rfl hp,
end

@[monotonic]
lemma ctx_p_and_entails_p_and_left (Γ p q x : pred' β)
  (h : ctx_impl Γ p q)
: ctx_impl Γ (p ⋀ x) (q ⋀ x) :=
by { lifted_pred using h,
     begin [smt] intros end }

@[monotonic]
lemma p_and_entails_p_and_left (p q x : pred' β)
  (h : p ⟹ q)
: p ⋀ x ⟹ q ⋀ x :=
by { lifted_pred using h,
     begin [smt] intros end }

@[monotonic]
lemma ctx_p_and_entails_p_and_right {Γ p q : pred' β} (x : pred' β)
  (h : ctx_impl Γ p q)
: ctx_impl Γ (x ⋀ p) (x ⋀ q) :=
by { lifted_pred using h,
     begin [smt] intros end }

@[monotonic]
lemma p_and_entails_p_and_right {p q : pred' β} (x : pred' β)
  (h : p ⟹ q)
: x ⋀ p ⟹ x ⋀ q :=
by { lifted_pred using h,
     begin [smt] intros end }

@[monotonic]
lemma ctx_p_not_entails_p_not_right {Γ p q : pred' β}
  (h : ctx_impl Γ q p)
: ctx_impl Γ (- p) (- q) :=
by { lifted_pred using h,
     begin [smt] intros end }

@[monotonic]
lemma p_not_entails_p_not_right {p q : pred' β}
  (h : q ⟹ p)
: - p ⟹ - q :=
by { lifted_pred using h,
     begin [smt] intros end }

lemma entails_of_eq (p q : pred' β)
  (h : p = q)
: p ⟹ q :=
by simp [h]

lemma equiv_of_eq (Γ p q : pred' β)
  (h : p = q)
: Γ ⊢ p ≡ q :=
by simp [h]

lemma p_and_entails_p_or (p q : pred' β)
: p ⋀ q ⟹ p ⋁ q :=
by { lifted_pred,
     begin [smt] intros end }

lemma True_p_imp (p : pred' β)
: True ⟶ p = p :=
by lifted_pred

lemma ew_eq_true {p : pred' β} : ⊩ p → p = True :=
by { intro h, lifted_pred using h,
     begin [smt] intros end }

@[monotonic]
lemma ew_imp_ew {p q : pred' β}
  (H : p ⟹ q)
: ⊩ p → ⊩ q :=
by { intros hp, lifted_pred using hp H, auto }

lemma entails_to_pointwise {p q : pred' β}
  (h : p ⟹ q)
: ∀ i, i ⊨ p → i ⊨ q :=
by { intros i h', apply (h (eq i)).apply i rfl h' }

lemma impl_of_p_impl {p q : pred' β} (i : β)
  (h : ⊩ p ⟶ q)
: i ⊨ p → i ⊨ q :=
entails_of_forall_impl h _

open interactive.types interactive
open lean.parser lean tactic (hiding funext)
meta def entails_or_ew {α : Type u} (t : expr) (tag : string)
   (ent_tac ew_tac : tactic α) : tactic α :=
do match t with
    | `(_ ⟹ _) := ew_tac
    | `(_ ⊢ _) := ent_tac
    | `(⊩ _) := ew_tac
    | _ := fail format!"expecting {tag} of shape `_ ⟹ _` or `⊩ _`"
   end

meta def pointwise (h : parse (many ident)) (ids : parse with_ident_list) : tactic unit :=
do t ← target,
   try $ entails_or_ew t "goal" `[refine revert_p_imp _,refine ew_wk _] `[refine ew_wk _],
   tactic.intro_lst ids,
   ls ← mmap get_local h,
   mmap' (λ l : expr,
    do entails_or_ew t "goal" (to_expr ``(ew_str (intro_p_imp %%l)))
                              (to_expr ``(ew_str %%l))
           >>= note l.local_pp_name none,
       try (clear l)) ls

run_cmd add_interactive [`pointwise]

lemma p_or_over_p_exists_left {t} (p : t → pred' β) (q : pred' β) {w : t → pred' β}
  (h : ⊩ ∃∃ x : t, w x)
: q ⋁ (∃∃ x, p x) = (∃∃ x, q ⋁ p x) :=
begin
  lifted_pred,
  have h := (h $ eq σ).apply _ rfl,
  have _inst : nonempty t := nonempty_of_exists h,
  simp [distrib_or_over_exists_left,p_exists,pred.p_exists],
end

@[congr]
lemma {v} p_exists_congr {α : Sort u} {β : Sort v} {p q : α → pred' β}
  (h : ∀ i, p i = q i)
: pred.p_exists p = pred.p_exists q :=
begin
  lifted_pred [pred.p_exists],
  rw [exists_congr],
  intro, rw h,
end

lemma p_and_over_p_exists_right {t} (p : t → pred' β) (q : pred' β)
: (∃∃ x, p x) ⋀ q = (∃∃ x, p x ⋀ q) :=
by lifted_pred

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
  begin [smt] split, all_goals { intros },
              by_cases (q.apply σ),
  end,
end

lemma shunting' {β : Sort*} (p q r : pred' β)
: p ⟶ (q ⟶ r) = (p ⋀ q) ⟶ r :=
by lifted_pred

lemma imp_swap {β : Sort*} (p q r : pred' β)
: p ⟶ (q ⟶ r) = q ⟶ (p ⟶ r) :=
by { lifted_pred,
     begin [smt] split, all_goals { intros }, end }

lemma entails_swap {β : Sort*} (p q r : pred' β)
: p ⟹ (q ⟶ r) ↔ q ⟹ (p ⟶ r) :=
by simp [p_entails,imp_swap]
-- ◻◇p ⊢ ◻◇q τ
-- `τ : stream σ, h : (◻◇p) τ ⊢ (◻◇q) τ`
lemma p_not_p_imp {β : Sort*} (p q : pred' β)
: (-p) ⟶ q = p ⋁ q :=
by rw [← True_p_and (-p),← shunting,True_p_imp]

lemma p_imp_iff_p_not_p_or {β : Sort*} (p q : pred' β)
: p ⟶ q = -p ⋁ q :=
by rw [← p_not_p_imp,p_not_p_not_iff_self]

lemma p_or_entails_p_or {p p' q q' : pred' β}
  (H₀ : p  ⟹ q )
  (H₁ : p' ⟹ q')
: p ⋁ p' ⟹ q ⋁ q' :=
by { pointwise H₀ H₁ with i h₀,
     apply or.imp (H₀ i) (H₁ i) h₀, }

@[monotonic]
lemma p_or_entails_p_or_left (p q x : pred' β)
: p ⟹ q → p ⋁ x ⟹ q ⋁ x :=
begin
  intros h, pointwise h with i h₀,
  simp at ⊢ h₀ ,
  apply or.imp_left (h _) h₀,
end

@[monotonic]
lemma ctx_p_or_entails_p_or_left (Γ p q x : pred' β)
: ctx_impl Γ p q → ctx_impl Γ (p ⋁ x) (q ⋁ x) :=
begin
  intros h, lifted_pred using h, -- with i h₀,
  begin [smt] intros, destruct a_1 end
end

lemma p_or_not_and {β : Sort*} (p q : pred' β)
: p ⋁ (- p ⋀ q) = p ⋁ q :=
begin
  lifted_pred,
  begin [smt]
    split,
    all_goals { intros h }, destruct h,
    by_cases (p.apply σ)
  end
end

lemma p_exists_intro {t : Sort u'} {p : t → pred' β} (x : t)
: p x ⟹ (∃∃ x, p x) :=
by { lifted_pred, apply exists.intro x, }

lemma p_exists_elim {t : Sort u'} {p : t → pred' β} {q : pred' β}
  (H : ∀ x, p x ⟹ q)
: (∃∃ x, p x) ⟹ q :=
begin
  pointwise with σ,
  simp, intro,
  apply entails_to_pointwise (H x) σ,
end

lemma p_exists_p_imp_p_exists {Γ : pred' β} {t : Sort u'} (p q : t → pred' β)
: Γ ⊢ (∀∀ x, p x ⟶ q x) → Γ ⊢ (∃∃ x, p x) ⟶ (∃∃ x, q x) :=
begin
  intros h,
  lifted_pred [- exists_imp_distrib],
  intro h',
  apply exists_imp_exists,
  intro x,
  apply h.apply _ h',
end

lemma p_exists_entails_p_exists {t : Sort u'} (p q : t → pred' β)
: (∀ x, p x ⟹ q x) → (∃∃ x, p x) ⟹ (∃∃ x, q x) :=
begin
  intros h _,
  apply p_exists_p_imp_p_exists,
  constructor, introv h' x,
  apply (h x Γ).apply _ h'
end

lemma p_exists_over_p_or {t} (p q : t → pred' β)
: (∃∃ x, p x) ⋁ (∃∃ x, q x) = (∃∃ x, p x ⋁ q x) :=
begin
  lifted_pred, split ; simp_intros
  ; cases a with a_1 a_1 ; revert a_1,
  { apply exists_imp_exists, intro, apply or.intro_left, },
  { apply exists_imp_exists, intro, apply or.intro_right, },
  apply or.imp ; apply Exists.intro a_1,
end

lemma p_exists_entails_p_exists' {t : Sort u₀} {t' : Sort u₁}
  (p : t → pred' β)
  (q : t' → pred' β)
  (f : t → t')
  (h : (∀ x, p x ⟹ q (f x)))
: (∃∃ x, p x) ⟹ (∃∃ x, q x) :=
begin
  intros,
  lifted_pred [- exists_imp_distrib],
  apply exists_imp_exists' f _ ,
  intro x,
  apply entails_to_pointwise (h x),
end

@[simp]
lemma p_exists_imp_eq_p_forall_imp
  (p : α → pred' β) (q : pred' β)
: ((∃∃ x, p x) ⟶ q) = (∀∀ x, p x ⟶ q) :=
by lifted_pred

lemma p_exists_entails_eq_p_forall_entails
  (p : α → pred' β) (q : pred' β)
: ((∃∃ x, p x) ⟹ q) ↔ (∀ x, p x ⟹ q) :=
by simp [p_entails,p_exists_imp_eq_p_forall_imp,ew_p_forall]

lemma p_exists_variable_change
  (p : α → pred' β) (q : γ → pred' β)
  (f : α → γ)
  (g : γ → α)
  (Hf : ∀ i, p i ⟹ q (f i))
  (Hg : ∀ j, q j ⟹ p (g j))
: (∃∃ i, p i) = (∃∃ j, q j) :=
begin
  lifted_pred [- exists_imp_distrib],
  rw exists_variable_change _ _ f g
  ; intro x
  ; apply entails_to_pointwise
  ; auto,
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

-- attribute [irreducible] p_not p_entails
-- attribute [trans]  entails_trans

end predicate
