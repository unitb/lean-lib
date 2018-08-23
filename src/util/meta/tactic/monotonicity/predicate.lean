
import util.logic

import util.meta.tactic.basic
import tactic.monotonicity

variables {a b c p : Prop}

namespace tactic.interactive

open lean lean.parser  interactive
open interactive.types -- expr
open tactic

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def ac_mono1 := ac_mono rep_arity.one none

meta def match_exists : expr → tactic (name × expr × expr)
 | `(@Exists _ %%e) := return (expr.binding_name e
                           ,expr.binding_domain e
                           ,expr.binding_body e)
 | _ := fail "expecting an existential"

meta def match_forall : expr → tactic (name × expr × expr)
 | (expr.pi n _ d b) := return (n,d,b)
 | e := fail $ format! "expecting a universal {e}"
-- #check forall_imp_forall _ _

/-- for goals of the form `f x → f x'` for certain monotonic or antimonotonic f,
    bring the context of `x` into the assumptions.
    Possible f are
      (∃ x, _)
      (∀ x, _)
      →, ∧, ∨, ¬
    TODO: add monotonicity type class
-/
meta def intro_mono (id : parse ident_ ?) : tactic unit :=
do g ← target >>= instantiate_mvars,
   match g with
    | `( (∃ x : %%t₀, %%e₀) → (∃ x : %%t₁, %%e₁) ) :=
      do (is_def_eq t₀ t₁
            <|> fail (format! "type of bound variables don't match: {t₀} ≠ {t₁}")),
         `[apply exists_imp_exists],
         intro id
    | `( (∀ x : %%t₀, %%e₀) → (∀ x : %%t₁, %%e₁) ) :=
        (do is_def_eq t₀ t₁,
            h' ← assert `h (expr.pi `x binder_info.default t₀ (e₀.imp $ e₁.lift_vars 0 1)),
            swap,
            h ← intro1,
            tactic.refine ``(@forall_imp_forall _ _ _ %%h' %%h),
            intro id)
    <|> (do (guard (¬ e₀.has_var ∧ ¬ e₁.has_var)
                   <|> fail (format! "type of bound variables don't match: {t₀} ≠ {t₁}")),
            is_def_eq e₀ e₁,
            p ← to_expr ``(%%t₁ → %%t₀),
            assert `h p,
            swap,
            `[intros h₀ h₁, apply h₀, apply h h₁])
    | `( (%%t₀ ∧ %%e₀) → (%%t₁ ∧ %%e₁) ) :=
        (do is_def_eq t₀ t₁,
            `[apply and.mono_right],
            intro id)
    <|> (do is_def_eq e₀ e₁,
            `[apply and.mono_left],
            intro id)
    | `( (%%t₀ ∨ %%e₀) → (%%t₁ ∨ %%e₁) ) :=
        (do is_def_eq t₀ t₁,
            `[apply classical.or.mono_right],
            intro id)
    <|> (do is_def_eq e₀ e₁,
            `[apply classical.or.mono_left],
            intro id)
    | `( (¬ %%e₀) → (¬ %%e₁) ) :=
        (`[apply mt])
    | _ := ac_mono1
   end

meta def intros_mono_dep : tactic unit :=
do g ← target,
   match g with
    | `(%%e₀ → %%e₁) :=
        (do (n₀,t₀,e₀) ← match_exists e₀,
            (n₁,t₁,e₁) ← match_exists e₁,
            if e₀.has_var_idx 0 then intro_mono (some n₀) >> intros_mono_dep
            else if e₁.has_var_idx 0 then intro_mono (some n₁) >> intros_mono_dep
            else return ())
    <|> (do (n₀,t₀,e₀) ← match_forall e₀,
            (n₁,t₁,e₁) ← match_forall e₁,
            if e₀.has_var_idx 0 then intro_mono (some n₀) >> intros_mono_dep
            else if e₁.has_var_idx 0 then intro_mono (some n₁) >> intros_mono_dep
            else return ())
    <|> (do expr.is_not e₀,
            expr.is_not e₁,
            intro_mono none,
            intros_mono_dep)
    <|> (do match_or e₀,
            match_or e₁,
            return ())
    <|> (do match_and e₀,
            match_and e₁,
            return ())
    <|> ac_mono1 >> intros_mono_dep
    <|> return ()
    | _ :=  ac_mono1 >> intros_mono_dep
        <|> return ()
   end

meta def introv_mono : parse ident_ * → tactic unit
 | [] := intros_mono_dep
 | (x::xs) := intros_mono_dep >> intro_mono (some x) >> introv_mono xs

meta def intros_mono : parse ident_ * → tactic unit
 | [] := repeat (intro_mono none)
 | xs := mmap' (intro_mono ∘ some) xs

end tactic.interactive
