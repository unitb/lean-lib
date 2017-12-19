
import data.stream
import util.control.applicative

namespace tactic

open tactic
open lean.parser
open interactive
open interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def local_def_value (e : expr) : tactic expr := do
do (v,_) ← solve_aux `(true) (do
         (expr.elet n t v _) ← (revert e >> target)
           | fail format!"{e} is not a local definition",
         return v),
   return v

meta def get_local_value (e : expr) : tactic (option expr) :=
try_core $ local_def_value e

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
  tactic.intros, reflexivity ),
rewrite_target h,
tactic.clear h

meta def unfold_locals : parse ident * → tactic unit
 | [] := return ()
 | (n::ns) := unfold_local n >> unfold_locals ns

@[user_attribute]
meta def funext_attribte : user_attribute :=
{ name := `extensionality
, descr := "lemmas usable by `funext` tactic" }

attribute [extensionality] funext stream.ext

meta def funext1 (x : parse ident_ ?) : tactic unit :=
do ls ← attribute.get_instances `extensionality,
   ls.any_of (λ l, applyc l) <|> fail "no applicable extensionality rule found",
   interactive.intro x

meta def funext : parse ident_ * → tactic unit
 | [] := return ()
 | (x :: xs) := funext1 x >> funext xs

open list

meta def clear_except (xs : parse ident *) : tactic unit :=
do r  ← list.mmap get_local xs >>= revert_lst,
   local_context >>= mmap (try ∘ tactic.clear),
   intron r

meta def match_head (e : expr) : expr → tactic unit
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

meta def xassumption (asms : option (list expr) := none) : tactic unit :=
do { ctx ← asms.to_monad <|> local_context,
     t   ← target,
     H   ← find_matching_head t ctx,
     tactic.apply H }
<|> fail "assumption tactic failed"

meta def auto (asms : option (list expr) := none) : tactic unit :=
xassumption asms ; xassumption asms ; xassumption asms ; done
open tactic.interactive
open applicative (lift₂)

meta def rw_aux (p : pos) (r : pexpr) (loc : loc) : tactic unit :=
do interactive.rw ⟨[rw_rule.mk p ff r ],none⟩ loc

meta def distrib1
  (arg : rw_rule)
  (loc : loc) : tactic unit :=
do let op := arg.rule,
   let p := arg.1,
   if arg.symm then
   ( rw_aux p ``(is_left_distrib.left_distrib _ %%op) loc <|>
     rw_aux p ``(is_right_distrib.right_distrib _ %%op) loc)
   else
   ( rw_aux p ``(is_left_distrib.left_distrib %%op) loc <|>
     rw_aux p ``(is_right_distrib.right_distrib %%op) loc),
   return ()

meta def distributivity
  (args : parse $ rw_rules)
  (l : parse location) : tactic unit :=
mmap' (λ e, distrib1 e l) args.rules

meta def interactive.replace
  (h : parse ident)
  (q₁ : parse (tk ":" *> texpr)?)
: parse ((tk ":=" *> texpr)?) → tactic unit
 | none := do h' ← get_local h,
              tactic.interactive.«have» h q₁ none
              ; [ skip , clear h' ]
 | (some pr) := do h' ← get_local h,
                   tactic.interactive.«have» h q₁ (some pr),
                   clear h'

end tactic

open tactic
run_cmd add_interactive [`auto,`xassumption,`unfold_local,`unfold_locals
                        ,`funext1,`tactic.funext,`clear_except
                        ,`distributivity]
