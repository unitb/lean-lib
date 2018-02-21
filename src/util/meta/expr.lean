import meta.expr
import util.data.traversable

universes u v

section expr
open expr

meta def expr.is_mvar : expr → bool
 | (expr.mvar _ _ _) := tt
 | _ := ff

meta def expr.list_meta_vars (e : expr) : list expr :=
e.fold [] (λ e' _ es, if expr.is_mvar e' ∧ ¬ e' ∈ es then e' :: es else es)

meta def expr.list_const (e : expr) : list expr :=
e.fold [] (λ e' _ es, if expr.is_constant e' ∧ ¬ e' ∈ es then e' :: es else es)

end expr
