
import data.list

namespace list

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}
variables x : α
variables xs ys : list α

def opt_head : list α → option α
 | [] := none
 | (x :: _) := some x

def front : list α → list α
  | [] := []
  | [x] := []
  | (x :: xs) := x :: front xs

lemma not_concat_eq_nil
: concat xs x ≠ [] :=
by { cases xs ; contradiction }

lemma front_concat
: front (concat xs x) = xs :=
begin
  induction xs with y ys IH,
  { refl },
  { unfold concat front,
    destruct (concat ys x),
    { intro h, cases not_concat_eq_nil _ _ h },
    { intros z zs Hconcat,
      rw Hconcat, unfold front,
      rw [← Hconcat,IH], }, }
end

variables {P : list α → Prop}

lemma ind_concat
  (Hnil : P nil)
  (Hcons : ∀ x xs, P xs → P (concat xs x))
: ∀ xs, P xs :=
begin
  let Q := P ∘ reverse,
  intro,
  rw ← reverse_reverse xs,
  generalize : (reverse xs) = ys, clear xs,
  change Q ys,
  induction ys with y ys IH,
  { apply Hnil },
  { change P _,
    have h := Hcons y (reverse ys) IH,
    rw [reverse_cons y ys,← concat_eq_append],
    apply h },
end

lemma rec_concat
  (Hnil : P nil)
  (Hcons : ∀ x xs, P (concat xs x))
: ∀ xs, P xs :=
begin
  apply ind_concat Hnil _,
  intros x xs IH,
  apply Hcons,
end

lemma ilast_concat {a : α} [inhabited α]
: ∀ (l : list α), ilast (concat l a) = a
  | [] := rfl
  | [x] := rfl
  | [x,y] := rfl
  | (x::y::z::l) := ilast_concat (z :: l)


lemma front_last_eq
  [inhabited α]
  (h₀ : xs ≠ []) (h₁ : ys ≠ [])
  (Hxs : front xs = front ys)
  (Hx : ilast xs = ilast ys)
: xs = ys :=
begin
  revert xs ys, intro,
  eapply   rec_concat _ _ xs,
  { intro, apply   rec_concat _ _ ys,
    contradiction,
    intros y ys h₀ h₁,
    contradiction, },
  { intros x xs ys,
    apply rec_concat _ _ ys,
    intro, contradiction,
    intros y ys h₀ h₁,
    rw [front_concat,front_concat,ilast_concat,ilast_concat],
    intros h₂ h₃,
    rw [h₂,h₃], }
end

section

variable {f : α → α → α}
variable [is_associative α f]
variable [is_commutative α f]
variable x₀ : α

lemma foldl_eq_foldr_of_ac
: foldl f x₀ xs = foldr f x₀ xs :=
begin
  induction xs,
  case nil
  { refl },
  case cons : x xs IH
  { unfold foldl foldr,
    rw ← IH, symmetry,
    rw [foldl_hom (f x) f f _ _ xs,is_commutative.comm f],
    { intros y z, rw is_associative.assoc f } },
end

end

lemma append_cons {α : Type u} (xs : list α) (x : α) (ys : list α)
: xs ++ x :: ys = (xs ++ [x]) ++ ys :=
by simp

instance {α : Type*} : monoid (list α) :=
{ mul := has_append.append
, one := []
, one_mul := nil_append
, mul_one := append_nil
, mul_assoc := append_assoc }

def mapp (f : α → β → γ) : list (α × β) → list γ
 | [ ] := [ ]
 | ((x,y) :: xs) := f x y :: mapp xs

end list
