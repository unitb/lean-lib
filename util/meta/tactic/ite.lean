
namespace interactive

open tactic

meta def loc.get_locations : loc → tactic (list expr)
| loc.wildcard := (::) <$> tactic.target <*> (tactic.local_context >>= mmap infer_type)
| (loc.ns xs)  := mmap (λ n, match n with
  | none :=   tactic.target
  | some n := tactic.get_local n >>= infer_type
  end) xs

end interactive

namespace tactic.interactive

open lean lean.parser  interactive
open interactive.types
open tactic

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def find_ite : expr → ℕ →
  option (bool × expr × expr) →
  option (bool × expr × expr)
| `(@ite %%c %%d %%α %%l %%r) i none :=
  if ¬ c.has_var then some (ff, c, d)
                 else none
| `(@dite %%c %%d %%α %%l %%r) i none :=
  if ¬ c.has_var then some (tt, c, d)
                 else none
| e i none := none
| _ _ (some e) := (some e)

meta def ite_cases (hyp : parse (tk "with" *> ident_) ?)
                   (ls : parse location)
: tactic unit :=
do g ← ls.get_locations >>= mmap instantiate_mvars,
   match list.foldl (λ r e, expr.fold e r find_ite) none g with
    | (some (_,e,d)) :=
      do hyp' ← get_unused_name $ option.cases_on hyp `h id,
         cases (none,to_pexpr d) [hyp',hyp']
         ; [ (do hyp' ← get_local hyp',
                 simp tt [ simp_arg_type.expr
                            ``(@dif_neg _ (is_false %%hyp') %%hyp')
                         , simp_arg_type.expr
                            ``(@if_neg _ (is_false %%hyp') %%hyp')]
                         [] ls)
           , do hyp' ← get_local hyp',
                simp tt [ simp_arg_type.expr
                           ``(@dif_pos _ (is_true %%hyp') %%hyp')
                        , simp_arg_type.expr
                           ``(@if_pos _ (is_true %%hyp') %%hyp')]
                        [] ls ]
    | none :=  fail "no conditionals found"
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

example (x y i j : ℕ)
  (f : ℕ → ℕ)
  (h'' : (if h : x ≤ y then x ≤ i else y ≤ j))
  (h''' : f (if h : x ≤ y then y else x) ≤ 7)
  (h'''' : (if h : x ≤ y then y else x) ≤ 7)
: (if h : x ≤ y then x else y) ≤ (if x ≤ y then i else j) :=
begin
  ite_cases with h₃ at ⊢ h'' h''',
  all_goals { assumption }
end

example (x y i j : ℕ)
  (f : ℕ → ℕ)
  (h'' : (if h : x ≤ y then x ≤ i else y ≤ j))
  (h''' : f (if h : x ≤ y then y else x) ≤ 7)
  (h'''' : (if h : x ≤ y then y else x) ≤ 7)
: x ≤ i ∨ y ≤ j :=
begin
  ite_cases with h₃ at ⊢ h'' h'''
  ; [ right , left ]
  ; assumption
end

end tactic.interactive
