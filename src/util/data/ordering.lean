
import algebra.order

universe u
variables {α : Type u}
variables [decidable_linear_order α]

lemma cmp_eq_eq (a b : α)
: cmp a b = ordering.eq = (a = b) :=
by { simp [cmp,cmp_using_eq_eq], rw ← le_antisymm_iff, cc }
