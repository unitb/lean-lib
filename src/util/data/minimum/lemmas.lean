
import util.meta.tactic

import util.data.minimum.basic

variable {α : Type*}
variable [has_minimum α]
open has_minimum (minimum)
lemma lt_minimum_iff (x : α) {xs : set α}
  (h : xs ≠ ∅)
: x < minimum xs ↔ (∀ y ∈ xs, x < y) :=
begin
  split,
  { intros, apply lt_of_lt_of_le a,
    apply minimum_le H, },
  { intros, apply_assumption,
    apply minimum_mem h },
end
