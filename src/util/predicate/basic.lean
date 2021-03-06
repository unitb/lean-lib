
import util.logic
import util.category
import util.meta.tactic.basic
import util.meta.tactic.monotonicity

run_cmd do
mk_simp_attr `predicate,
mk_simp_attr `lifted_fn

namespace predicate

universe variables u u' u₀ u₁ u₂

variables {α : Sort u₀}
variables {β : Sort u₁}
variables {γ : Sort u₂}
variables {σ : Sort u'}

structure var (α : Sort u₀) (β : Sort u₁) : Sort (max u₀ u₁+1) :=
  (apply : α → β)

attribute [pp_using_anonymous_constructor] var

@[simp, predicate]
def fun_app_to_var (f : α → β) : var σ α → var σ β
 | ⟨ g ⟩ := ⟨ f ∘ g ⟩

@[simp, predicate]
def combine_var : var σ (α → β) → var σ α → var σ β
 | ⟨ f ⟩ ⟨ x ⟩ := ⟨ λ s, f s (x s) ⟩

@[reducible]
def pred' (α : Sort u) : Type (max u 1) :=
var.{u 1} α Prop

def pred'.mk := @var.mk

notation x ` ⊨ `:53 y:52 := (var.apply y x)

structure judgement (h y : pred' α) : Prop :=
(apply : ∀ σ, σ ⊨ h → σ ⊨ y)

infix ` ⊢ `:53 := judgement

def lifted₀ (p : β) : var α β := ⟨ λ _, p ⟩
def lifted₁ (op : β → γ) (p : var α β) : var α γ :=
⟨ λ i, op (i ⊨ p) ⟩
def lifted₂ (op : α → β → γ) (p : var σ α) (q : var σ β) : var σ γ :=
⟨ λ i, op (i ⊨ p) (i ⊨ q) ⟩

attribute [simp, predicate] lifted₀ lifted₁ lifted₂
attribute [predicate] var.apply var.mk pred'.mk

-- def ew (p : pred' α) : Prop :=
-- ∀ i, i ⊨ p
@[predicate]
def False {α} : pred' α := lifted₀ false
@[predicate]
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

def p_impl (p₀ p₁ : pred' α) : pred' α :=
lifted₂ implies p₀ p₁

@[lifted_fn, reducible]
def v_eq : var α β → var α β → pred' α :=
lifted₂ eq

@[lifted_fn, reducible]
def p_equiv : pred' α → pred' α → pred' α :=
v_eq

def p_entails (p₀ p₁ : pred' α) : Prop :=
⊩ p_impl p₀ p₁

def p_not (p : pred' α) : pred' α :=
lifted₁ not p

def p_exists {β : Sort u'} {t : Sort u} (P : t → pred' β) : pred' β :=
⟨λ x, ∃ y, x ⊨ P y⟩

def p_forall {t : Sort u} {β : Sort u'} (P : t → pred' β) : pred' β :=
⟨ λ x, ∀ y, x ⊨ P y ⟩

notation `∃∃` binders `, ` r:(scoped P, p_exists P) := r
notation `∀∀` binders `, ` r:(scoped P, p_forall P) := r

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

instance var_functor {γ : Type _} : functor (var γ) :=
{ map := λ α β f x, ⟨ λ y, f $ x.apply y ⟩ }
instance var_has_seq {γ : Type _} : has_seq (var γ) :=
{ seq := λ α β f x, ⟨ λ s, f.apply s (x.apply s) ⟩ }
instance var_has_pure {γ : Type _} : has_pure (var γ) :=
{ pure := λ α x, ⟨ λ _, x ⟩ }
instance var_applicative {α : Type u} : applicative (var α) :=
{ ..predicate.var_functor
, ..predicate.var_has_seq
, ..predicate.var_has_pure }
instance var_has_bind {γ : Type _} : has_bind (var γ) :=
{ bind := λ α x ⟨ m ⟩ f, ⟨ λ i, (f $ m i).apply i ⟩ }
instance var_monad {γ : Type _} : monad (var γ) :=
{ ..predicate.var_applicative
, ..predicate.var_has_bind }

@[lifted_fn, reducible]
def v_lt {β : Type _} [has_lt β] : var α β → var α β → pred' α :=
lifted₂ (<)

@[lifted_fn, reducible]
def v_wf_r [has_well_founded β] : var α β → var α β → pred' α :=
lifted₂ has_well_founded.r

@[lifted_fn, reducible]
def v_le {β : Type _} [has_le β] : var α β → var α β → pred' α :=
lifted₂ (≤)

@[lifted_fn, reducible]
def v_mem {β : Type _} {γ : Type _} [has_mem β γ] : var α β → var α γ → pred' α :=
lifted₂ (∈)

infix ` ≃ `:75 := v_eq
infix ` ∊ `:75 := v_mem
infix ` ≺ `:75 := v_lt
infix ` ≼ `:75 := v_le
infix ` ≺≺ `:75 := v_wf_r
infix ` << `:50 := has_well_founded.r

def var_seq : var σ (α → β) → var σ α → var σ β
 | ⟨ f ⟩ ⟨ x ⟩ := ⟨ λ i, f i (x i) ⟩

instance val_to_var_coe : has_coe β (var α β) :=
{ coe := λ x, ⟨ λ _, x ⟩ }
instance option_val_to_var_coe {β} : has_coe β (var α (option β)) :=
{ coe := λ x, ↑(some x) }
instance var_coe_to_fun : has_coe_to_fun (var σ $ α → β) :=
{ F := λ _, var σ α → var σ β
, coe := var_seq }
def var_coe_to_fun₂ : has_coe_to_fun (var σ $ α → β → γ) :=
{ F := λ _, var σ α → var σ β → var σ γ
, coe := λ f x₀ x₁, f x₀ x₁ }
def var_coe_to_fun₃ {α₀ α₁ α₂} : has_coe_to_fun (var σ $ α₀ → α₁ → α₂ → β) :=
{ F := λ _, var σ α₀ → var σ α₁ → var σ α₂ → var σ β
, coe := λ f x₀ x₁ x₂, f x₀ x₁ x₂ }
def var_coe_to_fun₄ {α₀ α₁ α₂ α₃} : has_coe_to_fun (var σ $ α₀ → α₁ → α₂ → α₃ → β) :=
{ F := λ _, var σ α₀ → var σ α₁ → var σ α₂ → var σ α₃ → var σ β
, coe := λ f x₀ x₁ x₂ x₃, f x₀ x₁ x₂ x₃ }

abbreviation val_to_var : β → var α β :=
coe

notation `⟪ ` x ` ⟫` := (⟨ x ⟩ : var _ _)
notation `⟪ ` t, x ` ⟫` := (@val_to_var t _ x)

def proj : var β γ → var α β → var α γ
 | ⟨p⟩ ⟨f⟩ := ⟨p∘f⟩

infix ` ! `:90 := proj

@[simp, predicate, reducible]
def contramap (p : pred' α) (f : β → α) : pred' β :=
p ! ⟨ f ⟩

infixr ` '∘ `:90 := contramap

def whole : var α α := ⟨ @id α ⟩

end predicate
