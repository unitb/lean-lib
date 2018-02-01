
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

lemma inv_is_right_inverse_of_surjective
  (H : surjective f)
: right_inverse (inv f) f :=
begin
  simp [right_inverse,left_inverse,inv], intro,
  apply_epsilon_spec,
end

end function
