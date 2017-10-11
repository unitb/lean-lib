
import data.list.perm

namespace tactic.interactive

open tactic

private meta def is_cons : expr → option (expr × expr)
 | `(list.cons %%x %%xs) := some (x,xs)
 | _ := none

private meta def parse_list' (t : expr) : expr → tactic (list expr)
 | e := do
    (do (x,xs) ← is_cons e,
        list.cons x <$> parse_list' xs)
<|> (do guard (e.is_app_of `list.nil),
        return [])

private meta def parse_list (e : expr) : tactic (list expr) :=
do `(list %%t) ← infer_type e | fail (to_fmt "expecting a list type in " ++ to_fmt e),
   parse_list' t e <|> fail (to_fmt "expecting a list literal in " ++ to_fmt e)

meta def find (e : expr) : list expr → tactic (expr × list expr × list expr)
 | [] := tactic.fail "foo"
 | (x :: xs) :=
do b ← try_core (tactic.is_def_eq e x),
   if b.is_some then
     return (x,[],xs)
   else do
     (x',ys,xs') ← find xs,
     return (x',x::ys,xs')

meta def list_literal : list expr → tactic expr
 | [] := to_expr ``([])
 | (x :: xs) :=
do xs' ← list_literal xs,
   to_expr ``(%%x :: %%xs')

meta def mk_perm_proof : list expr → list expr → tactic expr
| [] ys :=
if ys = [] then
   to_expr ``(list.perm.nil)
else do
   ys' ← pp ys,
   fail $ to_fmt "unmatched left-over: " ++ ys'
| (x :: xs) ys := do
  x' ← pp x, ys' ← pp ys,
  (y,ys₀,ys₁) ← find x ys <|> fail (x' ++ " not found in " ++ ys'),
  left_p ← mk_perm_proof xs (ys₀ ++ ys₁),
  left ← to_expr ``(list.perm.skip %%x %%left_p),
  zs₀ ← list_literal ys₀,
  zs₁ ← list_literal ys₁,
  right_p ← to_expr ``(list.perm.perm_cons_app %%y %%zs₀),
  right ← to_expr ``(list.perm.perm_app_left %%zs₁ %%right_p),
  to_expr ``(list.perm.trans %%left %%right)

/-- prove a goal of the form `perm [a,b,c] [c,a,b]` -/
meta def prove_perm : tactic unit := do
  `(list.perm %%xs %%ys) ← target
      | fail "expecting goal of the form `(list.perm [...] [...])`",
  xs' ← parse_list xs,
  ys' ← parse_list ys,
  mk_perm_proof xs' ys' >>= tactic.apply

example : list.perm [1,2,3] [3,2,1] :=
by { prove_perm }

example : list.perm [1,2,3,4] [3,2,4,1] :=
by { prove_perm }

example : list.perm [1,2,3,4] [3,1,4] :=
by { success_if_fail { prove_perm }, admit }

example : list.perm [1,2,3,4] [3,2,4,5] :=
by { success_if_fail { prove_perm }, admit }

example : list.perm [1,2,3,4] [1,3,2,4,5] :=
by { success_if_fail { prove_perm }, admit }

example : list.perm [1,2,3,4] [1,3,2,4,5] :=
by { success_if_fail { prove_perm }, admit }

end tactic.interactive
