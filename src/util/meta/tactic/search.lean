open tactic environment

meta def search_some (s : expr → tactic bool) (hide : bool := tt) : tactic unit :=
do env ← get_env,
   env.fold (pure ()) $ λ d acc,
   do acc,
      declaration.thm n _ ty _ ← pure d | skip,
      when (hide ∧ n.last_string.front ≠ '_') $ do
        occ ← s ty,
        when occ $ do
          ty ← pp ty,
          trace $ to_fmt n ++ ": " ++ ty

meta def search_about (s : name) : tactic unit :=
do s ← resolve_constant s,
   search_some $ λ ty, return $ ty.fold ff (λ e _ acc, acc ∨ e.is_constant_of s)

meta def match_head (pat : pattern) : expr → tactic bool
 | ty :=
tt <$ match_pattern pat ty <|>
match ty with
 | (expr.pi n bi t e) := do l ← mk_local' n bi t, match_head (e.instantiate_var l)
 | _ := pure ff
end

meta def match_asm (pat : pattern) : expr → tactic bool
 | ty :=
match ty with
 | (expr.pi n bi t e) := do l ← mk_local' n bi t,
                            tt <$ match_pattern pat t
                               <|> match_asm (e.instantiate_var l)
 | _ := pure ff
end

meta def search (p : pexpr) : tactic unit :=
do new_p ← pexpr_to_pattern p,
   search_some $ λ ty, match_head new_p ty

meta def search_asm (p : pexpr) : tactic unit :=
do new_p ← pexpr_to_pattern p,
   search_some $ λ ty, match_asm new_p ty

def m_or {m : Type* → Type*} [monad m] (x y : m bool) : m bool :=
do b ← x,
   if b then pure tt else y

infixl ` || ` := m_or

meta def search_rw (p : pexpr) : tactic unit :=
do left_p ← pexpr_to_pattern ``(%%p = _),
   right_p ← pexpr_to_pattern ``(_ = %%p),
   search_some $ λ ty, match_head left_p ty || match_head right_p ty

-- run_cmd search_about `has_add
-- run_cmd search ``(_ = _)
-- run_cmd search_asm ``(_ ≤ 0)
-- run_cmd search_rw ``(_ + (_ + _))
