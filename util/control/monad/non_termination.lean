
import util.data.option
import util.data.nat
import util.logic

universes u v

structure nonterm (α : Type u) :=
  (run : ℕ → option α)
  (consistent : ∀ i j x, i ≤ j → run i = some x → run j = some x)

open nat

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

protected def le (x y : nonterm α) : Prop :=
∀ i v, run_to x i v → run_to y i v

instance : has_le (nonterm α) :=
⟨ nonterm.le ⟩

protected lemma le_refl (x : nonterm α)
: x ≤ x :=
begin
  cases x,
  intros i j H, apply H,
end

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

instance : weak_order (nonterm α) :=
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

section fix

parameters {α : Type u}
parameters {β : Type v}

parameter f : (α → nonterm β) → (α → nonterm β)

parameter f_continuous : ∀ n v,
  ∀ (v1 v2 : α → nonterm β),
    (∀ x, v1 x ≤ v2 x) →
    (∀ x, run_to (f v1 x) n v →
          run_to (f v2 x) n v)

 -- Hypothesis f_continuous : forall n v v1 x,
 --    runTo (f v1 x) n v
 --    -> forall (v2 : A -> computation B),
 --      (forall x, leq (proj1_sig (v1 x) n) (proj1_sig (v2 x) n))
 --      -> runTo (f v2 x) n v.

def fix_aux : ℕ → α → nonterm β
 | 0 := f (λ _, diverge)
 | (succ n) := f (fix_aux n)

include f_continuous
-- Lemma Fix'_ok : forall steps n x v, proj1_sig (Fix' n x) steps = Some v
--     -> forall n', n' >= n
--       -> proj1_sig (Fix' n' x) steps = Some v.
--     unfold runTo in *; induction n; crush;
--       match goal with
--         | [ H : _ >= _ |- _ ] => inversion H; crush; eauto
--       end.
--   Qed.
def fix_consistent (steps n : ℕ) (x : α) (y : β)
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
      apply f_continuous, intro,
      apply le_bottom } },
  { have hn' := le_of_succ_le hn,
    simp [fix_aux] at h,
    induction n' with n',
    { cases not_lt_zero _ hn },
    { have hnn' := le_of_succ_le_succ hn,
      simp [fix_aux] at *,
      revert h,
      apply f_continuous,
      intros z i yy hh,
      apply ih_1 i n' z _ hh hnn' } }
end

def fix (x : α) : nonterm β :=
{ run := λ i, (fix_aux i x).run i
, consistent :=
  begin
    introv h _,
    apply nonterm.consistent _ _ _ _ h,
    apply fix_consistent ; assumption,
  end }

lemma unroll
: fix = f fix := sorry

end fix

end nonterm

instance : monad nonterm :=
{ pure := @nonterm.pure
, bind := @nonterm.bind
, bind_assoc := @nonterm.bind_assoc
, pure_bind := @nonterm.pure_bind
, id_map := @nonterm.id_map }
