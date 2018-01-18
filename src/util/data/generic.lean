
import util.data.bijection
import util.control.monad
import util.control.applicative
import util.meta.tactic

universes u

class generic (α : Type u) :=
  (rep : Type u)
  (to_rep : α → rep)
  (of_rep : rep → α)
  (corresponence : bijection α rep)

export generic (rep)

attribute [reducible] generic.rep

meta def tactic.mk_sigma (v t : expr) : tactic expr :=
do t' ← tactic.infer_type v,
   tactic.to_expr ``(@sigma %%t' %%(expr.lambdas [v] t))

namespace tactic.interactive

open tactic

meta def mk_prod_rep' (α : expr) (c : name)
: list expr → expr → list expr → tactic (expr × expr × expr)
 | [] _ _ :=
   do c' ← mk_const c,
      let to_rep : expr := `(()),
      return (`(unit),to_rep,expr.lam `_ binder_info.default `(unit) c')
 | [x] e es := do c' ← mk_const c,
             t ← infer_type x,
             let of_rep := c'.mk_app (e :: es).reverse,
             return (t,x,expr.lambdas [e] of_rep)
 | (x :: xs) e es :=
    do xs' ← mmap infer_type xs,
       if (xs'.any (x.occurs)) then do
         t₀ ← infer_type x,
         v ← mk_mvar,
         y ← mk_local_def `x v,
         (t₁,to_rep,of_rep) ← mk_prod_rep' xs y (x :: es) <|> fail "mk_prod_rep'",
         unify v (t₁),
         of_rep ← instantiate_mvars of_rep,
         t ← mk_sigma x t₁,
         to_rep ← to_expr ``(sigma.mk %%x %%to_rep),
         of_rep ← to_expr ``(@sigma.cases_on %%t₀ %%((expr.lambdas [x] t₁)) (λ x, %%α) %%e (%%(expr.lambdas [x] of_rep)) : %%α),
         return (t,to_rep,expr.lambdas [e] of_rep)
       else do
         t₀ ← infer_type x,
         v ← mk_mvar,
         y ← mk_local_def `x v,
         (t₁,to_rep,of_rep) ← mk_prod_rep' xs y (x :: es),
         unify v t₁,
         t ← to_expr ``(%%t₀ × %%t₁),
         to_rep ← to_expr ``((%%x, %%to_rep)),
         of_rep ← to_expr ``(@prod.cases_on %%t₀ %%t₁ (λ _, %%α) %%e (%%(expr.lambdas [x] of_rep)) : %%α),
         return (t,to_rep,expr.lambdas [e] of_rep)

meta def mk_inr (α β : expr) (p : pexpr) : pexpr :=
``(@sum.inr %%α %%β %%p)

meta def mk_inl (α β : expr) (p : pexpr) : pexpr :=
``(@sum.inl %%α %%β %%p)

meta def mk_prod_rep (α : expr) (c : name) (f : list (name × expr × expr)) : tactic (expr × expr × expr) :=
do t ← resolve_name c >>= to_expr >>= infer_type,
   (cmp,_) ← mk_local_pis t,
   x ← mk_mvar >>= mk_local_def `x,
   (t,to_rep,of_rep) ← mk_prod_rep' α c cmp x [],
   to_rep' ← mfoldl ((λ e ⟨c,α,β⟩,
       do c' ← mk_const c,
          return (expr.mk_app c' [α,β,e])) : _ → _ × _ × _ → tactic expr) to_rep f,
   to_rep ← instantiate_mvars (expr.lambdas cmp to_rep'),
   return (t,to_rep,of_rep)

/-- `mk_sum_rep cs` returns
  - the representation type for constructors cs
  - a list of functions `to_rep` for the cases `cs`
  - a function of_rep (for the constructed rep type) to α -/
meta def mk_sum_rep (α : expr) : list (name × expr × expr) → list name → tactic (expr × list expr × expr)
 | f [] :=
 do of_rep ← to_expr ``(empty.rec_on (λ _, %%α) : empty → %%α),
    return (`(empty),[],of_rep)
 | f [x] := prod.map id (prod.map singleton id) <$> mk_prod_rep α x f
 | f (x::xs) :=
 do α' ← mk_mvar,
    β' ← mk_mvar,
    y  ← mk_prod_rep α x ((`sum.inl, α', β') :: f),
    ys ← mk_sum_rep ((`sum.inr, α', β') :: f) xs,
    rep ← to_expr ``(%%y.1 ⊕ %%ys.1),
    of_rep ← to_expr ``((λ x, @sum.cases_on %%α' %%β' (λ _, %%α) x %%y.2.2 %%ys.2.2) : %%rep → %%α),
    return (rep,y.2.1 :: ys.2.1,of_rep)

meta def prove_inverse : name → tactic unit | n :=
(`[simp ; try { congr }] ; reflexivity) <|>
do c ← resolve_name n >>= to_expr,
   t ← infer_type c,
   match t with
    | `(_ × _) := tactic.cases c [`x,`y] >> prove_inverse `y
    | `(Σ _, _) := tactic.cases c [`x,`y] >> prove_inverse `y
    | `(_ ⊕ _) := (() <$ tactic.cases c [`x,`x]) ; solve1 (prove_inverse `x)
    | `(unit) :=  tactic.cases c >> reflexivity
    | _ := fail "cannot prove inverse"
   end

meta def mk_generic_instance : tactic unit :=
do `(generic %%t) ← target,
   e ← get_env,
   let n := t.const_name,
   let ns := n <.> "generic",
   set_env $ e.add_namespace ns,
   (rep,to_rep,of_rep) ← mk_sum_rep t [] (e.constructors_of t.const_name),
   cases_on ← resolve_name (t.const_name <.> "cases_on") >>= to_expr,
   x ← mk_local_def `x t,
   let to_rep' := expr.lambdas [x] $ cases_on.mk_app (x::to_rep),
   bij_t ← to_expr ``(bijection %%t %%rep),
   bij ← assert `bij bij_t,
   swap,
   d ← to_expr ``( { generic . rep := %%rep
                   , to_rep := %%to_rep'
                   , of_rep := %%of_rep
                   , corresponence := %%bij } : generic %%t ),
   instantiate_mvars d >>= tactic.apply,
   `[apply @bijection.mk %%t %%rep %%to_rep' %%of_rep],
   solve1 `[intro x, induction x ; refl ],
   solve1 (intro `x >> prove_inverse `x)

end tactic.interactive

instance finite_generic (α : Type u) [generic α] [finite (rep α)] : finite α :=
⟨ finite.count (rep α) , finite.to_nat _ ∘ generic.corresponence α ⟩

instance pos_finite_generic (α : Type u) [generic α] [pos_finite (rep α)] : pos_finite α :=
⟨ pos_finite.pred_count (rep α) , pos_finite.to_nat _ ∘ generic.corresponence α ⟩

instance infinite_generic (α : Type u) [generic α] [infinite (rep α)] : infinite α :=
⟨ infinite.to_nat _ ∘ generic.corresponence α ⟩

instance : generic bool :=
by mk_generic_instance

instance : finite bool :=
finite_generic _

namespace examples

inductive generic_ex1 : Type
 | case1 : generic_ex1
 | case2 : generic_ex1
 | case3 : ℕ → generic_ex1
 | case4 : bool → ℕ → generic_ex1

open generic_ex1

instance : generic generic_ex1 :=
by mk_generic_instance

inductive generic_ex2 : Type
 | case1 : generic_ex2
 | case2 : ℕ → ℕ → bool → generic_ex2
 | case3 (n : ℕ) : fin n → generic_ex2
 | case4 : bool → generic_ex2

instance generic_generic_ex2 : generic generic_ex2 :=
begin mk_generic_instance end

end examples
