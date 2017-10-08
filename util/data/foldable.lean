
import data.lazy_list

universes u v w

namespace lazy_list

variables {α : Type u}
variables {r : Type v}

open nat

def length : lazy_list α → ℕ
 | nil := 0
 | (cons x xs) := succ $ length (xs ())

@[simp] def nth_le : Π (l : lazy_list α) (n), n < l.length → α
| nil        n     h := absurd h (not_lt_zero n)
| (cons a l) 0     h := a
| (cons a l) (n+1) h := nth_le (l ()) n (le_of_succ_le_succ h)

def foldr (f : α → r → r) : lazy_list α → r → r
 | nil r := r
 | (cons x xs) r := f x (foldr (xs ()) r)

def foldl (f : α → r → r) : lazy_list α → r → r
 | nil r := r
 | (cons x xs) r := foldl (xs ()) (f x r)

end lazy_list

class foldable (f : Type u → Type v) extends functor f :=
  (size : ∀ {α}, f α → ℕ)
  (fold : ∀ {α} (x : f α), fin (size x) → α)
  (idx : ∀ {α} (x : f α), f (ulift $ fin (size x)))
  (correct_fold : ∀ {α} (x : f α), map (λ i, (fold x) (ulift.down i)) (idx x) = x)
  (to_lazy_list : ∀ {α}, f α → lazy_list α)
  (size_eq_length : ∀ {α} (x : f α), size x = (to_lazy_list x).length)
  (to_lazy_list_eq_fold : ∀ {α} (x : f α) i
       (h  : i < (to_lazy_list x).length),
       fold x ⟨i,eq.mp (by rw size_eq_length) h⟩ = (to_lazy_list x).nth_le i h)

export foldable (size fold idx correct_fold to_lazy_list)

namespace foldable

def foldr' {f : Type u → Type v} [i : foldable f] {r : Type w} {α : Type u} (g : α → r → r)
: f α → r → r :=
lazy_list.foldr g ∘ to_lazy_list

def foldr {f : Type u → Type v} [i : foldable f] {r : Type w} {α : Type u} (g : α → r → r)
: r → f α → r :=
flip (foldr' g)

def foldl {f : Type u → Type v} [i : foldable f] {r : Type w} {α : Type u} (g : α → r → r)
: f α → r → r :=
lazy_list.foldl g ∘ to_lazy_list

def to_list {f : Type u → Type v} [i : foldable f] {α : Type u} : f α → list α :=
@foldr f i _ _ list.cons []

def to_set' {f : Type u → Type v} [i : foldable f] {α : Type u} {r : Type u}
  [has_insert α r]
  [has_emptyc r]
: f α → r :=
@foldr f i _ _ insert ∅

def to_set {f : Type u → Type v} [i : foldable f] {α : Type u}
: f α → set α :=
@to_set' f i _ _ _ _

def fold_map {f : Type u → Type v} [i : foldable f] {m : Type w} [monoid m] {α : Type u}
  (g : α → m)
: f α → m :=
@foldr f i _ _ (has_mul.mul ∘ g) 1

def fold_map_add {f : Type u → Type v} [i : foldable f] {m : Type w} [add_monoid m] {α : Type u}
  (g : α → m)
: f α → m :=
@foldr f i _ _ (has_add.add ∘ g) 0

end foldable
