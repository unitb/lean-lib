
universes u v

structure nonterm (α : Type u) :=
  (run : ℕ → option α)
  (consistent : ∀ i j x, i ≤ j → run i = some x → run j = some x)

namespace nonterm

variables {α β γ : Type u}

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

open nat

def fix_aux {β : Type v} (f : (α → nonterm β) → (α → nonterm β)) : ℕ → (α → nonterm β)
 | 0 := f (λ _, diverge)
 | (succ n) := f (fix_aux n)

def fix {β : Type v} (f : (α → nonterm β) → (α → nonterm β)) (x : α) : nonterm β :=
{ run := λ i, (fix_aux f i x).run i
, consistent :=
  begin
    introv h₀ h₁,
    rw [← nat.add_sub_cancel_left i j,nat.add_sub_assoc h₀],
    generalize : j - i = k,
    induction k,
    case zero
    { simp, apply h₁ },
    case succ k
    { simp [add_succ],
      apply nonterm.consistent _ (i+k) _ _ (le_succ _),
      unfold fix_aux, admit }
  end }

lemma unroll {β : Type v} (f : (α → nonterm β) → (α → nonterm β))
: fix f = f (fix f) := sorry

def yields (x : nonterm α) (y : α) : Prop :=
∃ i, x.run i = some y

infix ` ~> `:55 := yields

end nonterm

instance : monad nonterm :=
{ pure := @nonterm.pure
, bind := @nonterm.bind
, bind_assoc := @nonterm.bind_assoc
, pure_bind := @nonterm.pure_bind
, id_map := @nonterm.id_map }
