
import util.classical

universes u v

variables {α : Type u}
variables {β : Type v}
variables {p q : α → Prop}
variables Hall : ∀ x, p x → q x
variables Hex : ∃ x, p x

lemma some_spec_test1
: p (classical.some Hex) :=
by apply_some_spec


section
include Hall

lemma some_spec_test2
: q (classical.some Hex) :=
by apply_some_spec

end

variables Hpq : ∀ x, p x → q x
lemma Hex : ∃ x, p x := sorry
open classical
include Hpq
variable [nonempty α]
example : q (ε x, p x) :=
begin
  apply_epsilon_spec Hex,
end
