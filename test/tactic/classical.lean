
import util.classical

universes u v

variables {α : Type u}
variables {β : Type v}
variables {p q : α → Prop}
variables Hall : ∀ x, p x → q x
variables Hex : ∃ x, p x

lemma some_spec_test1
: p (classical.some Hex) :=
by { apply_some_spec with w, }

include Hall

lemma some_spec_test2
: q (classical.some Hex) :=
by { apply_some_spec with w, apply Hall w }
