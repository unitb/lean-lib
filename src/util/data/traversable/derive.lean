
import util.data.traversable.basic

universes u v w w'

section list
variables {α : Type u} {β : Type v} {γ : Type w}
variables {m : Type w → Type w'}
variables [applicative m]

def mzip_with (f : α → β → m γ) : list α → list β → m (list γ)
 | (x :: xs) (y :: ys) := (::) <$> f x y <*> mzip_with xs ys
 | _ _ := pure []

def mzip_with' (f : α → β → m γ) : list α → list β → m punit
 | (x :: xs) (y :: ys) := f x y *> mzip_with' xs ys
 | _ _ := pure punit.star

end list

namespace tactic.interactive

open tactic list monad functor

meta def traverse_field (n : name) (cl' f v e : expr) : tactic (option expr) :=
do `(compose %%cl ulift) ← return cl' | failed,
   t ← infer_type e >>= whnf,
   if t.get_app_fn.const_name = n
   then return none
   else if v.occurs t
   then   (is_def_eq t v >> some <$> to_expr ``(compose.mk %%(expr.app f e)) )
      <|> (guard (¬ v.occurs (t.app_fn)) >> some <$> to_expr ``(compose.mk (has_traverse.traverse' %%f %%e)))
      <|> fail format!"type {t} is not traversable with respect to variable {v}"
   else
         (is_def_eq t.app_fn cl >> some <$> to_expr ``(compose.mk %%e))
     <|> some <$> to_expr ``(@pure %%cl' _ _ %%e)

meta def seq_apply_constructor : list expr → expr → tactic expr
 | (x :: xs) e := to_expr ``(%%e <*> %%x) >>= seq_apply_constructor xs
 | [] e := return e

meta def fill_implicit_arg' : expr → expr → tactic expr
 | f (expr.pi n bi d b) :=
if b.has_var then
do v ← mk_meta_var d,
   fill_implicit_arg' (expr.app f v) (b.instantiate_var v)
else return f
 | e _ := return e

meta def fill_implicit_arg (n : name) : tactic expr :=
do c ← mk_const n,
   t ← infer_type c,
   fill_implicit_arg' c t

meta def traverse_constructor (c n : name) (f v : expr) (args : list expr) : tactic unit :=
do applyc `compose.run,
   g ← target,
   args' ← mmap (traverse_field n g.app_fn f v) args,
   constr ← fill_implicit_arg c,
   constr' ← to_expr ``(@pure %%(g.app_fn) _ _ %%constr),
   r ← seq_apply_constructor (filter_map id args') constr',
   () <$ tactic.apply r

meta def derive_traverse : tactic unit :=
do `(has_traverse %%f) ← target | failed,
   env ← get_env,
   let n := f.get_app_fn.const_name,
   let cs := env.constructors_of n,
   constructor,
   `[intros m _ α β f x],
   x ← get_local `x,
   xs ← tactic.induction x,
   f ← get_local `f,
   α ← get_local `α,
   β ← get_local `β,
   m ← get_local `m,
   () <$ mzip_with'
      (λ (c : name) (x : _ × _ × _), solve1 (traverse_constructor c n f α x.2.1))
      cs xs

end tactic.interactive
