
import data.stream

namespace stream

open nat

lemma map_app {α β} (f : α → β) (s : stream α) (i : ℕ)
: stream.map f s i = f (s i) := rfl

def sprefix {α} : ℕ → stream α → list α
  | 0 _ := []
  | (succ n) x := x 0 :: sprefix n (stream.tail x)

def sums (x : stream ℕ) : stream ℕ
  | 0 := 0
  | (succ n) := x n + sums n

def range : ℕ → list ℕ
  | 0 := []
  | (succ n) := n :: range n

def prepend {α} : list α → stream α → stream α
  | [] xs := xs
  | (list.cons x xs) ys := stream.cons x (prepend xs ys)

def coinduct {α β} (f : α → (β × α)) (x : α) : stream β
  := stream.corec (prod.fst ∘ f) (prod.snd ∘ f) x

def rounds.f : ℕ × ℕ → ℕ × ℕ × ℕ
  | (n, 0) := (0, succ n, succ n)
  | (n, succ p) := (succ p, n, p)

lemma stream.head_corec {α β} (f : α → α) (g : α → β) (x : α) :
  stream.head (stream.corec g f x) = g x :=
begin
  refl
end

-- print nat.rec
-- set_option pp.implicit true
section s

universe variables u

variables {α β : Type u} (f : α → α) (g : α → β) (x : α)
variables i : ℕ
variables s : stream α

lemma stream.nth_tail : stream.nth i (stream.tail s) = stream.nth (succ i) s := rfl

lemma stream.tail_corec :
  stream.tail (stream.corec g f x) = stream.corec g f (f x) :=
begin
  apply stream.ext, intro i,
  unfold stream.corec,
  rw [stream.map_iterate,stream.tail_map,stream.tail_iterate],
  rw [stream.map_iterate],
end


theorem head_drop : head (drop i s) = nth i s :=
begin
  change nth 0 (drop i s) = _,
  rw nth_drop 0 i s,
  simp
end

end s

universe variables u₀ u₁

variables {α : Type u₀}
variables {β : Type u₁}

def zip' (x : stream α) (y : stream β) : stream (α × β) :=
λ i, (x i, y i)

lemma fst_comp_zip' (x : stream α) (y : stream β)
: prod.fst ∘ zip' x y = x := rfl

end stream
