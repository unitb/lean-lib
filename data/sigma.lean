
universe variables u v

variables {α : Type u} {β : α → Type v}

variables {x y : sigma β}
variables H  : x.1 = y.1
variables H' : x.1 = y.1 → x.2 == y.2

include H H'

lemma sigma.ext : x = y :=
begin
  cases x with x₀ x₁,
  cases y with y₀ y₁,
  have H'' := H' H, clear H',
  unfold sigma.fst at H,
  unfold sigma.snd at H'',
  subst y₀,
  rw eq_of_heq H'',
end
