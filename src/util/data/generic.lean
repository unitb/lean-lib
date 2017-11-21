
import util.data.bijection

universes u

class generic (α : Type u) :=
  (rep : Type u)
  (to_rep : α → rep)
  (of_rep : rep → α)
  (corresponence : bijection α rep)

attribute [reducible] generic.rep

meta def tactic.mk_sigma (v t : expr) : tactic expr :=
do t' ← tactic.infer_type v,
   tactic.to_expr ``(@sigma %%t' %%(expr.lambdas [v] t))

namespace tactic.interactive

open tactic

-- #check empty.rec_on
#check @sigma.rec
-- #check @prod.rec

meta def mk_prod_rep' (α : expr) (c : name) : list expr → tactic (expr × expr × expr)
 | [] := do c' ← mk_const c, return (`(unit),`(()),expr.lam `_ binder_info.default `(unit) c')
 | [x] := do c' ← mk_const c,
             t ← infer_type x,
             return (t,x,c')
 | (x :: xs) :=
    do xs' ← mmap infer_type xs,
       if (xs'.any (x.occurs)) then do
         t₀ ← infer_type x,
         (t₁,to_rep,of_rep) ← mk_prod_rep' xs,
         t ← mk_sigma x t₁,
         to_rep ← to_expr ``(sigma.mk %%x %%to_rep),
         of_rep ← to_expr ``(@sigma.rec _ _ (λ x, %%α) (λ x y, %%of_rep x y) : %%t → %%α),
         return (t,to_rep,of_rep)
       else do
         t₀ ← infer_type x,
         (t₁,to_rep,of_rep) ← mk_prod_rep' xs,
         t ← to_expr ``(%%t₀ × %%t₁),
         to_rep ← to_expr ``((%%x, %%to_rep)),
         of_rep ← to_expr ``(@prod.rec _ _ (λ _, %%α) (λ x y, %%of_rep x y) : %%t → %%α),
         return (t,to_rep,of_rep)

meta def mk_prod_rep (α : expr) (c : name) : tactic (expr × expr × expr) :=
do t ← resolve_name c >>= to_expr >>= infer_type,
   (cmp,_) ← mk_local_pis t,
   (t,to_rep,of_rep) ← mk_prod_rep' α c cmp,
   return (t,expr.pis cmp to_rep,of_rep)

/-- `mk_sum_rep cs` returns
  - the representation type for constructors cs
  - a list of functions `to_rep` for the cases `cs`
  - a function of_rep (for the constructed rep type) to α -/
meta def mk_sum_rep (α : expr) : list name → tactic (expr × list expr × expr)
 | [] :=
 do of_rep ← to_expr ``(empty.rec_on (λ _, %%α)),
    return (`(empty),[],of_rep)
 | [x] := prod.map id (prod.map singleton id) <$> mk_prod_rep α x
 | (x::xs) :=
 do y  ← mk_prod_rep α x,
    ys ← mk_sum_rep xs,
    rep ← to_expr ``(%%y.1 ⊕ %%ys.1),
    of_rep ← to_expr ``((λ x, sum.cases_on x %%y.2.2 %%ys.2.2) : %%rep → %%α),
    return (rep,y.2.1 :: ys.2.1,of_rep)

-- #print prefix sum

meta def mk_generic_instance : tactic unit :=
do `(generic %%t) ← target,
   e ← get_env,
   let ns := t.const_name <.> "generic",
   set_env $ e.add_namespace ns,
   (rep,to_rep,of_rep) ← mk_sum_rep t (e.constructors_of t.const_name),
   rec ← resolve_name (t.const_name <.> "rec") >>= to_expr,
   d ← to_expr ``( { generic . rep := %%rep
                   , to_rep := %%(rec.mk_app to_rep)
                   , of_rep := %%of_rep
                   , corresponence := sorry } : generic %%t ),
   tactic.exact d

end tactic.interactive

inductive generic_ex1 : Type
 | case1 : generic_ex1
 | case2 : generic_ex1
 | case3 : ℕ → generic_ex1
 | case4 : bool → ℕ → generic_ex1

instance : generic generic_ex1 :=
by mk_generic_instance

inductive generic_ex2 : Type
 | case1 : generic_ex2
 | case2 : generic_ex2
 | case3 (n : ℕ) : fin n → generic_ex2
 | case4 : bool → generic_ex2

instance : generic generic_ex2 :=
by mk_generic_instance
