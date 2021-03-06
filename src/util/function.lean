
import util.classical

universes u v

namespace function

variables {α : Type u} {β : Type v}
variables [nonempty α]
variables (f : α → β)

noncomputable def inv (y : β) : α :=
ε x, f x = y

variable {f}
lemma inv_is_left_inverse_of_injective
  (H : injective f)
: left_inverse (inv f) f :=
begin
  simp [left_inverse,inv], intro,
  apply_epsilon_spec,
end

lemma inv_eq (x : α) (y : β)
  (H : injective f)
  (h : y = f x)
: inv f y = x :=
by rw [h,inv_is_left_inverse_of_injective H]

lemma injective_of_left_inverse_inv
  (h : left_inverse (inv f) f)
: injective f :=
injective_of_left_inverse h

lemma inv_is_right_inverse_of_surjective
  (H : surjective f)
: right_inverse (inv f) f :=
begin
  simp [right_inverse,left_inverse,inv], intro,
  apply_epsilon_spec,
end

end function
