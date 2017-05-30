
universe variables u

section

parameters {α : Type u}
parameters [weak_order α]
parameters x y : α

lemma indirect_eq_left_iff
: x = y ↔ (∀ z, z ≤ x ↔ z ≤ y) :=
begin
  split ; intro h,
  { subst y, intro, refl },
  apply @le_antisymm α,
  { rw -h },
  { rw h },
end

lemma indirect_eq_right_iff
: x = y ↔ (∀ z, x ≤ z ↔ y ≤ z) :=
begin
  split ; intro h,
  { subst y, intro, refl },
  apply @le_antisymm α,
  { rw h },
  { rw -h },
end

lemma indirect_le_left_iff
: x ≤ y ↔ (∀ z, z ≤ x → z ≤ y) :=
begin
  split ; intro h,
  { intro z, apply flip le_trans h, },
  { apply h, refl },
end

lemma indirect_le_right_iff
: x ≤ y ↔ (∀ z, y ≤ z → x ≤ z) :=
begin
  split ; intro h,
  { intro z, apply le_trans h, },
  { apply h, refl },
end

parameters {x y}

lemma eq_of_indirect_left_iff
  (h : ∀ z, z ≤ x ↔ z ≤ y)
: x = y :=
indirect_eq_left_iff.mpr h

lemma eq_of_indirect_eq_right
  (h : ∀ z, x ≤ z ↔ y ≤ z)
: x = y :=
indirect_eq_right_iff.mpr h

lemma le_of_indirect_le_left
  (h : ∀ z, z ≤ x → z ≤ y)
: x ≤ y :=
indirect_le_left_iff.mpr h

lemma le_of_indirect_le_right
  (h : ∀ z, y ≤ z → x ≤ z)
: x ≤ y :=
indirect_le_right_iff.mpr h

parameter z : α

lemma indirect_left_left_of_eq
  (h : x = y)
: z ≤ x ↔ z ≤ y :=
indirect_eq_left_iff.mp h z

lemma indirect_eq_right_of_eq
  (h : x = y)
: x ≤ z ↔ y ≤ z :=
indirect_eq_right_iff.mp h z

lemma indirect_le_left_of_le
  (h : x ≤ y)
: z ≤ x → z ≤ y :=
indirect_le_left_iff.mp h z

lemma indirect_le_right_of_le
  (h : x ≤ y)
: y ≤ z → x ≤ z :=
indirect_le_right_iff.mp h z

end
