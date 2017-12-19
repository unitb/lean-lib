
import util.predicate

namespace tactic
open predicate

meta def atoms : expr → dlist expr
 | e@`(%%p → %%q) :=
    if q.has_var
    then dlist.singleton e
    else  atoms p ++ atoms q
 | `(%%p ↔ %%q) := atoms p ++ atoms q
 | `(%%p ∨ %%q) := atoms p ++ atoms q
 | `(%%p ∧ %%q) := atoms p ++ atoms q
 | `(¬ %%p) := atoms p
 | v := dlist.singleton v

meta def try_abstract (e : expr) : tactic (list expr) :=
(generalize e >> list.ret <$> intro1) <|> return []

open nat smt_tactic (eblast solve_goals)
open smt_tactic.interactive (rsimp)

meta def show_prop : tactic unit :=
do p ← target,
   vs ← list.join <$> mmap try_abstract (atoms p).to_list,
   ctx ← local_context, mmap' (try ∘ clear) ctx.reverse,
   using_smt (rsimp <|> (smt_tactic.intros ; eblast))
open interactive (loc)
open tactic.interactive (simp)
meta def propositional : tactic unit :=
do `(_ ⟹ _) ← target | show_prop,
   `[pointwise with v,simp],
   try show_prop

end tactic

run_cmd add_interactive [`tactic.propositional]
