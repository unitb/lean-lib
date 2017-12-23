
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

meta def split_or (xs : list expr) : smt_tactic (list expr) :=
do cs ← local_context,
   h ← mmap (λ h, try_core $ do
     t ← infer_type h,
     h <$ (match_or t <|> match_and t))
   $ cs.diff xs,
  let h' := h.filter_map id,
  h' <$ mmap' smt_tactic.destruct h'

meta def split_all_or' : list expr → smt_tactic unit
 | xs := do ys ← split_or xs, (guard (¬ ys.empty) >> smt_tactic.all_goals (split_all_or' (ys ++ xs))) <|> return ()

meta def split_all_or : smt_tactic unit :=
split_all_or' []

meta def show_prop : tactic unit :=
-- do p ← target,
--    vs ← list.join <$> mmap try_abstract (atoms p).to_list,
--    ctx ← local_context, mmap' (try ∘ clear) ctx.reverse,
   using_smt ((smt_tactic.intros ; split_all_or ; eblast))

open interactive (loc)
open tactic.interactive (simp)

meta def propositional : tactic unit :=
do t ← target,
   match t with
    | `(_ ⟹ _) := `[pointwise with v,simp with predicate] >> try show_prop
    | `(_ = _) := `[lifted_pred] >> split ; try show_prop
    | `(_ ⊢ _) := `[pointwise with v,simp with predicate] >> try show_prop
    | `(⊩ _) := `[pointwise with v,simp with predicate] >> try show_prop
    | _ := show_prop
  end

end tactic

meta def smt_tactic.interactive.break_asms : smt_tactic unit :=
tactic.split_all_or

run_cmd add_interactive [`tactic.propositional]
