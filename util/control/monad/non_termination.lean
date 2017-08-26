
import util.data.option
import util.data.nat
import util.logic

universes u u' v w

structure nonterm (α : Type u) :=
  (run : ℕ → option α)
  (consistent : ∀ i j x, i ≤ j → run i = some x → run j = some x)

open nat function

namespace nonterm

section instances

variables {α β γ : Type u}

def run_to (m : nonterm α) (n : ℕ) (x : α) :=
m.run n = some x

def yields (x : nonterm α) (y : α) : Prop :=
∃ i, run_to x i y

infix ` ~> `:55 := yields

protected def pure (x : α) : nonterm α :=
{ run := λ i, some x
, consistent := by { introv h h', apply h' } }

protected def bind (x : nonterm α) (f : α → nonterm β) : nonterm β :=
{ run := λ i, x.run i >>= λ j, (f j).run i
, consistent :=
  begin
    introv h h',
    destruct x.run i,
    { intro h₂, rw h₂ at h', contradiction },
    { intros z h₂,
      simp [h₂,bind,option_bind] at h',
      simp [x.consistent _ _ _ h h₂,bind,option_bind],
      apply (f z).consistent _ _ _ h h' }
  end }

instance : has_bind nonterm := ⟨ @nonterm.bind ⟩
instance : has_pure nonterm := ⟨ @nonterm.pure ⟩

protected lemma run_to_bind (i : ℕ) (x : nonterm α) (f : α → nonterm β) (v : β)
: run_to (x >>= f) i v ↔ (∃ v', run_to x i v' ∧ run_to (f v') i v) :=
sorry

lemma id_map (x : nonterm α)
: x >>= pure ∘ id = x :=
begin
  cases x,
  unfold has_bind.bind nonterm.bind nonterm.run,
  tactic.congr,
  apply funext, intro i,
  unfold function.comp id,
  apply @monad.bind_pure _ α option,
end

lemma pure_bind (x : α) (f : α → nonterm β)
: pure x >>= f = f x :=
begin
  unfold pure bind nonterm.bind has_pure.pure nonterm.pure nonterm.run option_bind,
  destruct (f x),
  introv h, simp [h],
end

lemma bind_assoc (x : nonterm α) (f : α → nonterm β) (g : β → nonterm γ)
: x >>= f >>= g = x >>= (λ i, f i >>= g) :=
begin
  cases x,
  unfold bind nonterm.bind nonterm.run,
  tactic.congr,
  apply funext, intro i,
  destruct (run i),
  { intro h, simp [h,option_bind], },
  { intros x h, simp [h,option_bind] }
end

def diverge : nonterm α :=
{ run := λ _, none
, consistent := by { intros, contradiction } }

lemma run_diverge (x : α)
: ¬ diverge ~> x :=
begin
  unfold yields, intro H,
  cases H with i H,
  unfold diverge run_to nonterm.run at H,
  contradiction,
end

def assert (p : Prop) [decidable p] : nonterm (plift p) :=
if H : p then pure ⟨ H ⟩ else diverge

protected lemma ext (x y : nonterm α)
  (h : ∀ i v, run_to x i v ↔ run_to y i v)
: x = y :=
begin
  cases x with x Hx, cases y with y Hy,
  tactic.congr,
  apply funext, intro i,
  unfold run_to at h,
  destruct (x i),
  destruct (y i),
  { intros h₀ h₁, rw [h₀,h₁] },
  { intros x' h₀ h₁,
    unfold nonterm.run at h,
    rw [← h i x',h₁] at h₀,
    contradiction },
  { intros x' h₀,
    unfold nonterm.run at h,
    rw h₀,
    rw [h i x'] at h₀,
    rw h₀ },
end

protected def le (x y : nonterm α) : Prop :=
∀ i v, run_to x i v → run_to y i v

instance : has_le (nonterm α) :=
⟨ nonterm.le ⟩

@[refl]
protected lemma le_refl (x : nonterm α)
: x ≤ x :=
begin
  cases x,
  intros i j H, apply H,
end

@[trans]
protected lemma le_trans (x y z : nonterm α)
  (h₀ : x ≤ y)
  (h₁ : y ≤ z)
: x ≤ z :=
begin
  intros i v h₂,
  apply h₁,
  apply h₀ _ _ h₂,
end

protected lemma le_antisymm (x y : nonterm α)
  (h₀ : x ≤ y)
  (h₁ : y ≤ x)
: x = y :=
begin
  cases x with x hx,
  cases y with y hy,
  tactic.congr,
  apply funext, intro i,
  destruct (y i),
  destruct (x i),
  { intros h₂ h₃, simp [h₂,h₃] },
  { intros v h₂ h₃, rw h₂,
    symmetry, apply h₀, apply h₂ },
  { intros v h₂, rw h₂,
    apply h₁, apply h₂ },
end

instance : partial_order (nonterm α) :=
{ le := nonterm.le
, le_refl := nonterm.le_refl
, le_trans := nonterm.le_trans
, le_antisymm := nonterm.le_antisymm }

lemma le_bottom (x : nonterm α)
: diverge ≤ x :=
by { intros i v h, unfold diverge run_to at h, contradiction }

def orelse_run (x y : nonterm α) : ℕ → option α
 | 0 := x.run 0 <|> y.run 0
 | (succ i) := orelse_run i <|> x.run (succ i) <|> y.run (succ i)

protected def orelse (x y : nonterm α) : nonterm α :=
{ run := λ i, nonterm.orelse_run x y i
, consistent :=
  begin
    intros i j v Hij h,
    rw [← nat.add_sub_cancel_left i j,nat.add_sub_assoc Hij],
    generalize : j - i = k,
    induction k with k,
    { apply h },
    { dsimp [add_succ,nonterm.orelse_run],
      simp [ih_1] }
  end }

instance : has_orelse nonterm :=
⟨ @nonterm.orelse ⟩

end instances

end nonterm

class has_mono (m : Type u → Type v)
extends monad m :=
  (le : ∀ {α}, partial_order (m α))
  (input_t  : Type v)
  (result_t : Type u → Type v)
  (run_to : ∀ {α}, m α → ℕ → input_t → result_t α → Prop)
  (run_to_imp_run_to_of_le : ∀ {α} (x y : m α) i v₀ v,
     x ≤ y → run_to x i v₀ v → run_to y i v₀ v)

export has_mono (run_to input_t result_t run_to_imp_run_to_of_le)

instance fix_partial_order {m α} [has_mono m] : partial_order (m α) :=
has_mono.le _

section monotonic

variable {m : Type v → Type w}
variable [has_mono m]
variable {α : Type u}
variable {β : Type v}

section mono1

variable f : (α → m β) → (α → m β)

def monotonic := ∀ n v v',
  ∀ (v1 v2 : α → m β),
    (∀ x, v1 x ≤ v2 x) →
    (∀ x, run_to (f v1 x) v n v' →
          run_to (f v2 x) v n v')

end mono1

variable {γ : Type u'}

@[inline]
def uncurry' (f : α → β → γ) : α × β → γ :=
λ (x : α × β), f x.1 x.2

variable f : (α → γ → m β) → α → γ → m β

def monotonic2 :=
monotonic (λ rec, uncurry' $ f $ curry rec)

end monotonic

instance : monad nonterm :=
{ pure := @nonterm.pure
, bind := @nonterm.bind
, bind_assoc := @nonterm.bind_assoc
, pure_bind := @nonterm.pure_bind
, id_map := @nonterm.id_map }

instance : has_mono.{u} nonterm :=
{ le := by apply_instance
, to_monad := by apply_instance
, result_t := λ α, α
, input_t  := ulift unit
, run_to := λ α x y z, nonterm.run_to x y
, run_to_imp_run_to_of_le := by { introv _ h, cases x, cases y, apply h } }

namespace nonterm

section fix

parameters {α : Type u}
parameters {β : Type v}

parameter f : (α → nonterm β) → (α → nonterm β)
parameter f_monotonic : monotonic f

def fix_aux : ℕ → α → nonterm β
 | 0 := f (λ _, diverge)
 | (succ n) := f (fix_aux n)

include f_monotonic

lemma fix_consistent (steps n : ℕ) (x : α) (y : β)
  (h : run_to (fix_aux n x) steps y )
  (n' : ℕ)
  (hn : n ≤ n')
: run_to (fix_aux n' x) steps y :=
begin
  revert steps n' x y,
  induction n with n ; intros steps n' x y h hn,
  { unfold fix_aux at h,
    induction n' with n',
    { simp [fix_aux], apply h },
    { simp [fix_aux], revert h,
      apply f_monotonic, exact ⟨ () ⟩,
      intro,
      apply le_bottom } },
  { have hn' := le_of_succ_le hn,
    simp [fix_aux] at h,
    induction n' with n',
    { cases not_lt_zero _ hn },
    { have hnn' := le_of_succ_le_succ hn,
      simp [fix_aux] at *,
      revert h,
      apply f_monotonic,
      exact ⟨ () ⟩,
      intros z i yy hh,
      apply ih_1 i n' z _ hh hnn' } }
end

protected def fix (x : α) : nonterm β :=
{ run := λ i, (fix_aux i x).run i
, consistent :=
  begin
    introv h _,
    apply nonterm.consistent _ _ _ _ h,
    apply fix_consistent ; assumption,
  end }

lemma unroll_a (x : α)
: nonterm.fix x ≤ f nonterm.fix x :=
begin
  intros i v,
  dunfold nonterm.fix,
  unfold run_to nonterm.run,
  induction i with i,
  { unfold fix_aux,
    apply f_monotonic, exact ⟨ () ⟩,
    intro, apply le_bottom, },
  { unfold fix_aux,
    apply f_monotonic, exact ⟨ () ⟩,
    intros x j v hh,
    dunfold run_to nonterm.fix nonterm.run,
    cases le_total i j with Hij Hji,
    { apply nonterm.consistent _ _ _ _ Hij, admit
      /- unfold fix nonterm.run, apply hh -/ },
    { admit } }
end

lemma unroll_b (x : α) (v : β)
  (h : f fix x ~> v)
: fix x ~> v :=
begin
  cases h with i h,
  unfold yields, existsi (succ i),
  dunfold run_to fix nonterm.run fix_aux,
  apply nonterm.consistent _ i,
  { apply le_succ },
  revert h, apply f_monotonic,
  exact ⟨ () ⟩,
  intros x j v,
  dunfold run_to fix nonterm.run,
  induction j with j,
  { intro h,
    induction i with i,
    { apply h },
    unfold fix_aux, admit },
  admit,
end

end fix

end nonterm

section monotonic

parameters {α : Type u} {β γ φ : Type v}
open nonterm

section

parameters f' : (α → nonterm β) → α → nonterm β
parameters g' : (α → nonterm β) → α → β → nonterm β
parameters Hf' : monotonic (λ rec x, f' rec x)
parameters Hg' : ∀ y, monotonic (λ rec x, g' rec x y)
include Hf' Hg'

protected lemma bind_monotonic
: monotonic (λ rec x, f' rec x >>= g' rec x) :=
begin
  intros i₀ i y v1 v2 Hlt x,
  simp [has_mono.run_to,nonterm.run_to_bind],
  apply exists_imp_exists,
  intros v',
  apply and.imp,
  { apply Hf' ⟨ () ⟩, apply Hlt },
  { apply Hg' _ ⟨ () ⟩, apply Hlt }
end
end

section

parameters {m : Type v → Type w}
parameters f  : α → m γ
parameters hf : has_mono m
include hf

lemma pure_monotonic
: monotonic (λ rec, f) :=
by { introv Hlt x H, apply H }

end
section

parameters f  : α → nonterm γ
parameters g  : (α → nonterm β) → α → γ → nonterm β
parameters Hg  : ∀ y, monotonic (λ rec x, g rec x y)

include Hg

protected lemma bind_monotonic'
: monotonic (λ rec x, f x >>= g rec x) :=
begin
  intros i₀ i y v1 v2 Hlt x,
  simp [has_mono.run_to,nonterm.run_to_bind],
  apply exists_imp_exists,
  intros v',
  apply and.imp_right,
  apply Hg _ ⟨ () ⟩, apply Hlt
end
end

parameter {m : Type v → Type u}
parameter [has_mono m]

section

parameters {f' : α → α}

lemma rec_monotonic
: monotonic (λ rec x, (rec (f' x) : m β)) :=
begin
  intros i₀ i y v1 v2 Hlt x,
  apply run_to_imp_run_to_of_le, apply Hlt
end
end

section

parameter {p : α → Prop}
parameter [decidable_pred p]
parameter {t : (α → m β) → α → m β}
parameter {f : (α → m β) → α → m β}

open plift

parameter Ht : monotonic t
parameter Hf : monotonic f
include Ht Hf

lemma dite_monotonic
: monotonic (λ (rec : α → m β) x, dite (p x) (λ _, t rec x) (λ _, f rec x)) :=
begin
  intros i₀ i y v1 v2 Hlt x,
  simp,
  by_cases p x with h,
  { simp [dif_pos h], apply Ht, apply Hlt },
  { simp [dif_neg h], apply Hf, apply Hlt },
end

lemma ite_monotonic
: monotonic (λ (rec : α → m β) x, ite (p x) (t rec x) (f rec x)) :=
begin
  have h := dite_monotonic,
  simp [dif_eq_if] at h,
  apply h,
end

end

end monotonic

section tactic

open tactic

meta def parse_monotonic : expr → tactic unit
 | `(monotonic %%f) := return ()
 | `(monotonic2 %%f) := return ()
 | `(auto_param %%e₀ %%e₁) := `[unfold auto_param] >> target >>= parse_monotonic
 | _ := fail "expecting monotonic"

meta def prove_monotonicity : tactic unit := do
target >>= parse_monotonic,
t ← target >>= instantiate_mvars,
solve1
( `[apply rec_monotonic]
<|>
  `[apply pure_monotonic]
<|>
  (do `[apply ite_monotonic],
      solve1 (prove_monotonicity),
      solve1 (prove_monotonicity))
<|>
  (do `[apply dite_monotonic],
      solve1 prove_monotonicity,
      solve1 prove_monotonicity)
<|>
  (do `[apply has_fix.bind_monotonic'],
      solve1 (intro1 >> prove_monotonicity))
<|>
  (do `[apply has_fix.bind_monotonic],
      solve1 prove_monotonicity,
      solve1 (intro1 >> prove_monotonicity))
<|>
  fail (to_fmt "can't prove: " ++ to_fmt t))

end tactic

class has_fix (m : Type u → Type v) extends has_mono m :=
  (mfix : ∀ {α : Type v} {β : Type u} (f : (α → m β) → α → m β), monotonic f → α → m β)
  (pre_fixpoint : ∀ {α β} (f : (α → m β) → α → m β) (h : monotonic f) (x : α),
      mfix f h x ≤ f (mfix f h) x)
  (bind_monotonic :
   ∀ {α : Type v} {β} (f' : (α → m β) → α → m β)
           (g' : (α → m β) → α → β → m β),
     monotonic (λ rec x, f' rec x) →
     (∀ y, monotonic (λ rec x, g' rec x y)) →
     monotonic (λ rec x, f' rec x >>= g' rec x))
  (bind_monotonic' :
   ∀ {α : Type v} {β γ} (f : α → m γ)
             (g : (α → m β) → α → γ → m β),
     (∀ y, monotonic (λ rec x, g rec x y)) →
     monotonic (λ rec x, f x >>= g rec x))

export has_fix (mfix)

section monotonic2

variable {m : Type v → Type (max u u')}
variable [has_fix m]
variable {α : Type u}
variable {β : Type v}
variable {γ : Type u'}

variable f : (α → γ → m β) → α → γ → m β

def mfix2 (h : monotonic2 f) (x : α) (y : γ) : m β :=
mfix (λ rec, uncurry' $ f $ curry rec) h (x, y)

end monotonic2

notation `fix`  f := mfix  f (by prove_monotonicity)
notation `fix2` f := mfix2 f (by prove_monotonicity)

instance : has_fix nonterm :=
  { to_has_mono := by apply_instance
  , mfix := @nonterm.fix
  , pre_fixpoint := @nonterm.unroll_a
  , bind_monotonic  := @bind_monotonic
  , bind_monotonic' := @bind_monotonic' }

export has_fix (mfix pre_fixpoint bind_monotonic bind_monotonic')

section setoid

parameter {α : Type u}

def same_result (x y : nonterm α) : Prop :=
∀ i, x ~> i ↔ y ~> i

local infix ` ≺ `:50 := same_result

variables {x y z : nonterm α}

@[refl]
lemma res_refl
: x ≺ x := by { intro, refl }

lemma res_symmetry
  (h : x ≺ y)
: y ≺ x := by { intro, simp [h i] }

@[trans]
lemma res_trans
  (h₀ : x ≺ y)
  (h₁ : y ≺ z)
: x ≺ z := by { intro, simp [h₀ i,h₁ i] }

instance : setoid (nonterm α) :=
 { r := same_result
 , iseqv := mk_equivalence _ @res_refl @res_symmetry @res_trans  }

end setoid

def partial (α : Type u) := quot (@same_result α)

class monad_fix (m : Type u → Type v) extends has_fix m :=
  (unroll_mfix : ∀ {α β} (f : (α → m β) → α → m β) (h : monotonic f) (x : α),
      f (mfix f h) x = mfix f h x)
