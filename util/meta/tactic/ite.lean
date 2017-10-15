
namespace tactic.interactive

open lean lean.parser  interactive
open interactive.types
open tactic

meta def find_ite : expr → ℕ →
  option (bool × expr × expr × expr × expr) →
  option (bool × expr × expr × expr × expr)
| `(@ite %%c %%d %%α %%l %%r) i none :=
  if ¬ c.has_var then some (ff, c, d, l, r)
                 else none
| `(@dite %%c %%d %%α %%l %%r) i none :=
  if ¬ c.has_var then some (tt, c, d, l, r)
                 else none
| e i none := none
| _ _ (some e) := (some e)

meta def ite_cases (hyp : parse (tk "with" *> ident)) : tactic unit :=
do g ← target,
   match expr.fold g none find_ite with
    | (some (_,e,d,l,r)) :=
      do cases (none,to_pexpr d) [hyp,hyp]
         ; [ (do hyp ← get_local hyp,
                 simp tt [ simp_arg_type.expr
                            ``(@dif_neg _ (is_false %%hyp) %%hyp)
                         , simp_arg_type.expr
                            ``(@if_neg _ (is_false %%hyp) %%hyp)]
                         [] (loc.ns [none]))
           , do hyp ← get_local hyp,
                simp tt [ simp_arg_type.expr
                           ``(@dif_pos _ (is_true %%hyp) %%hyp)
                        , simp_arg_type.expr
                           ``(@if_pos _ (is_true %%hyp) %%hyp)]
                        [] (loc.ns [none]) ]
    | none :=  fail "no conidition found"
   end

example (x y : ℕ)
  (h : x ≤ 7)
  (h' : y ≤ 7)
: (if x ≤ y then x else y) ≤ 7 :=
begin
  ite_cases with h₃,
  all_goals { assumption }
end

example (x y : ℕ)
  (h : x ≤ 7)
  (h' : y ≤ 7)
: (if h'' : x ≤ y then x else y) ≤ 7 :=
begin
  ite_cases with h₃,
  all_goals { assumption }
end

example (x y i j : ℕ)
  (h : x ≤ i)
  (h' : y ≤ j)
: (if h : x ≤ y then x else y) ≤ (if x ≤ y then i else j) :=
begin
  ite_cases with h₃,
  all_goals { assumption }
end

example (x y i j : ℕ)
  (h : x ≤ i)
  (h' : y ≤ j)
: (if x ≤ y then x else y) ≤ if (if x ≤ y then tt else ff) then i else j :=
begin
  ite_cases with h₃,
  all_goals { assumption }
end

end tactic.interactive
