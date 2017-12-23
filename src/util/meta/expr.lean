import util.data.traversable

universes u v

section expr
open expr
variables {m : Type → Type u} [applicative m]
variables {elab elab' : bool}

variables f : expr elab → m (expr elab')

meta def expr.traverse : expr elab → m (expr elab')
 | (var v)  := pure $ var v
 | (sort l) := pure $ sort l
 | (const n ls) := pure $ const n ls
 | (mvar n n' e) := mvar n n' <$> f e
 | (local_const n n' bi e) := local_const n n' bi <$> f e
 | (app e₀ e₁) := app <$> f e₀ <*> f e₁
 | (lam n bi e₀ e₁) := lam n bi <$> f e₀ <*> f e₁
 | (pi n bi e₀ e₁) := pi n bi <$> f e₀ <*> f e₁
 | (elet n e₀ e₁ e₂) := elet n <$> f e₀ <*> f e₁ <*> f e₂
 | (macro mac es) := macro mac <$> traverse f es

meta def expr.is_mvar : expr → bool
 | (expr.mvar _ _ _) := tt
 | _ := ff

meta def expr.list_meta_vars (e : expr) : list expr :=
e.fold [] (λ e' _ es, if expr.is_mvar e' ∧ ¬ e' ∈ es then e' :: es else es)

meta def expr.list_const (e : expr) : list expr :=
e.fold [] (λ e' _ es, if expr.is_constant e' ∧ ¬ e' ∈ es then e' :: es else es)

meta def expr.list_local_const (e : expr) : list expr :=
e.fold [] (λ e' _ es, if expr.is_local_constant e' ∧ ¬ e' ∈ es then e' :: es else es)

end expr
