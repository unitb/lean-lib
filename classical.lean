
universe variables u v

namespace classical

variables {α : Type u}
variables {β : Type v}
variables {p q : α → Prop}
variables Hpq : ∀ x, p x → q x
variables Hex : ∃ x, p x

include Hpq

lemma some_spec'
: q (some Hex) :=
begin
  apply Hpq,
  apply some_spec
end

end classical
