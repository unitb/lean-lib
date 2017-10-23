
namespace tactic.interactive

open tactic
open lean.parser
open interactive
open interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def unfold_local (n : parse ident) : tactic unit := do
e ← resolve_name n >>= to_expr,
g ← target,
t ← infer_type e,
v ← mk_meta_var t,
h ← to_expr ``(%%e = (%%v : %%t)) >>= assert `h,
solve1 (do
  tactic.revert e,
  g ← target,
  match g with
   | (expr.elet n _ e b) := tactic.change (expr.instantiate_local n e b)
   | _ := fail $ to_string n ++ " is not a local definition"
  end,
  tactic.intros, refl ),
rewrite_target h,
tactic.clear h

meta def unfold_locals : parse ident * → tactic unit
 | [] := return ()
 | (n::ns) := unfold_local n >> unfold_locals ns

meta def funext1 (x : parse ident_ ?) : tactic unit := do
`[apply funext],
intro x

meta def funext : parse ident_ * → tactic unit
 | [] := return ()
 | (x :: xs) := funext1 x >> funext xs

open list

meta def clear_except (xs : parse ident *) : tactic unit :=
do r  ← list.mmap get_local xs >>= revert_lst,
   local_context >>= mmap (try ∘ tactic.clear),
   intron r

private meta def match_head (e : expr) : expr → tactic unit
| e' :=
    unify e e'
<|> match e' with
     | `(_ → %%e') :=
     do v ← mk_mvar,
        match_head (e'.instantiate_var v)
     | _ := failed
    end

meta def find_matching_head : expr → list expr → tactic expr
| e []         := failed
| e (H :: Hs) :=
  do t ← infer_type H,
     (match_head e t >> return H) <|> find_matching_head e Hs

meta def xassumption : tactic unit :=
do { ctx ← local_context,
     t   ← target,
     H   ← find_matching_head t ctx,
     tactic.apply H }
<|> fail "assumption tactic failed"

meta def auto : tactic unit :=
xassumption ; xassumption ; assumption

end tactic.interactive
