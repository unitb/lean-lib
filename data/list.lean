
namespace list

universe variable u

variables {α : Type u}
variables x : α
variables xs ys : list α

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
      rw [-Hconcat,IH], }, }
end

variables {P : list α → Prop}

lemma ind_concat
  (Hnil : P nil)
  (Hcons : ∀ x xs, P xs → P (concat xs x))
: ∀ xs, P xs :=
begin
  let Q := P ∘ reverse,
  intro,
  rw -reverse_reverse xs,
  generalize (reverse xs) ys, clear xs,
  intros ys,
  change Q ys,
  induction ys with y ys IH,
  { apply Hnil },
  { change P _,
    have h := Hcons y (reverse ys) IH,
    rw [-reverse_cons y ys] at h,
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
  revert xs ys,
  apply   rec_concat _ _,
  { apply   rec_concat _ _,
    contradiction,
    intros y ys h₀ h₁,
    contradiction, },
  { intros x xs,
    apply rec_concat _ _,
    intro, contradiction,
    intros y ys h₀ h₁,
    rw [front_concat,front_concat,ilast_concat,ilast_concat],
    intros h₂ h₃,
    rw [h₂,h₃], }
end

end list
