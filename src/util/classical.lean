
import meta.expr
import util.meta.tactic

universe variables u v

notation `ε` binders `, ` r:(scoped p, classical.epsilon p) := r

namespace classical

variables {α : Type u}
variables {β : Type v}
variables {p q : α → Prop}
variables Hpq : ∀ x, p x → q x
variables Hex : ∃ x, p x

include Hpq Hex

lemma some_spec'
: q (some Hex) :=
begin
  apply Hpq,
  apply some_spec
end

variable [nonempty α]

lemma epsilon_spec'
: q (epsilon p) :=
begin
  apply Hpq,
  apply epsilon_spec Hex,
end

end classical

open tactic interactive interactive.types lean.parser

meta def apply_some_spec (id : parse $ optional (tk "with" *> ident_)) : tactic unit :=
do t ← target,
   (l,_) ← solve_aux t (do
     e ← to_expr ``(classical.some _),
     v ← mk_fresh_name,
     generalize e v,
     (expr.pi v bi t e) ← target,
     return (expr.lam v bi t e)),
   refine ``(@classical.some_spec' _ _ %%l _ _),
   `[simp only],
   interactive.intro id,
   try `[intros h, apply h]

meta def apply_epsilon_spec (ex : parse $ optional texpr)
  (id : parse $ optional (tk "with" *> ident_)) : tactic unit :=
focus1 $
do t ← target,
   (l,_) ← solve_aux t (do
     e ← to_expr ``(classical.epsilon _),
     v ← mk_fresh_name,
     generalize e v,
     (expr.pi v bi t e) ← target,
     return (expr.lam v bi t e)),
   refine ``(@classical.epsilon_spec' _ _ %%l _ _ _),
   `[simp only],
   interactive.intro id,
   try `[intros h, apply h],
   all_goals (auto <|> ↑ex >>= tactic.refine <|> return ())

run_cmd add_interactive [`apply_some_spec,`apply_epsilon_spec]
