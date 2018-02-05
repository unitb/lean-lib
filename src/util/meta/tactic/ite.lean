
import util.meta.tactic.basic

import algebra.order

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
                 simp none tt [ simp_arg_type.expr
                                ``(@dif_neg _ (is_false %%hyp') %%hyp')
                              , simp_arg_type.expr
                                ``(@if_neg _ (is_false %%hyp') %%hyp')]
                              [] ls
                       {constructor_eq := ff} )
           , do hyp' ← get_local hyp',
                simp none tt [ simp_arg_type.expr
                               ``(@dif_pos _ (is_true %%hyp') %%hyp')
                             , simp_arg_type.expr
                               ``(@if_pos _ (is_true %%hyp') %%hyp')]
                             [] ls
                      {constructor_eq := ff} ]
    | none :=  fail "no conditionals found"
   end

section lemmas
universe u
variables {α : Type u}
variables [decidable_linear_order α]

lemma cmp_eq_eq (a b : α)
: cmp a b = ordering.eq = (a = b) :=
by { simp [cmp,cmp_using_eq_eq], rw ← le_antisymm_iff, cc }

end lemmas

meta def ordering_cases
     (p : parse cases_arg_p)
     (pos : parse cur_pos)
     (hyp : parse (tk "with" *> ident)?)
: tactic unit :=
do `(cmp %%x %%y) ← to_expr p.2 | fail "expecting expression of shape `cmp _ _`",
   h₀ ← p.1 <|> mk_unique_name `this,
   let mk_asm : pexpr → tactic unit :=
     λ e,
      (do h₀ ← get_local h₀,
          h₁ ← (hyp : tactic name) <|> mk_unique_name `h,
          to_expr ``((%%e).mp %%h₀) >>=
            note h₁ none,
          interactive.rewrite ⟨[⟨pos,ff,``(%%h₀)⟩],none⟩ loc.wildcard,
          when p.1.is_none $ tactic.clear h₀,
          return ()),
   interactive.cases (some h₀,p.2) []
   ; [ mk_asm ``(cmp_using_eq_lt %%x %%y)
     , mk_asm ``(cmp_eq_eq %%x %%y)
     , mk_asm ``(cmp_using_eq_gt %%x %%y) ]

end tactic.interactive
