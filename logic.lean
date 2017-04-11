
universe variable u

lemma forall_imp_forall {α : Sort u} {p q : α → Prop}
   (h : ∀ a, (p a → q a))
   (p : ∀ a, p a) : ∀ a, q a :=
  take a, h _ (p a)

lemma imp_mono {p p' q q' : Prop}
   (hp : p' → p)
   (hq : q  → q')
   (h' : p → q) : (p' → q') := hq ∘ h' ∘ hp

lemma imp_imp_imp_left {p q r : Prop} (h : p → q)
   (h' : q → r) : (p → r) :=
take h'', h' (h h'')

lemma imp_imp_imp_right {p q r : Prop} (h : p → q)
   (h' : r → p) : (r → q) :=
take h'', h (h' h'')

lemma imp_imp_imp_right' {p q r : Prop} (h : r → p → q)
   (h' : r → p) : (r → q) :=
take h'', h h'' (h' h'')

variables {a b c : Prop}

lemma distrib_left_or : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) :=
begin
  split,
  { intro h,
    cases h with ha hb,
    { split, apply or.inl ha^.left, apply or.inl ha^.right },
    { split, apply or.inr hb, apply or.inr hb, } },
  { intro h,
    cases h with hb hc,
    cases hb with hb ha,
    cases hc with hc ha,
    { apply or.inl (⟨hb,hc⟩ : a ∧ b) },
    apply or.inr ha,
    apply or.inr ha, }
end

lemma not_or_of_not_and_not {p q : Prop} : ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
begin
  intro h,
  split ; intro h' ; apply h,
  { left, apply h' },
  { right, apply h' },
end

lemma not_and_not_of_not_or {p q : Prop} : ¬ p ∧ ¬ q → ¬ (p ∨ q) :=
begin
  intro h, cases h with hnp hnq,
  intro hpq,
  cases hpq with hp hq,
  { apply hnp hp },
  { apply hnq hq },
end

lemma not_or_iff_not_and_not {p q : Prop} : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
⟨not_or_of_not_and_not,not_and_not_of_not_or⟩

lemma not_and_of_not_or_not {p q : Prop} : ¬ (p ∧ q) → ¬ p ∨ ¬ q :=
begin
  intros h,
  cases classical.em p with hp hnp,
  { apply or.inr, intro hq, apply h, exact ⟨hp,hq⟩ },
  { apply or.inl hnp, }
end

lemma not_or_not_of_not_and {p q : Prop} : ¬ p ∨ ¬ q → ¬ (p ∧ q) :=
begin
  intro h,
  cases h with hnp hnq
  ; intro hpq ; cases hpq with hp hq,
  { apply hnp hp },
  { apply hnq hq },
end

lemma not_and_iff_not_or_not {p q : Prop} : ¬ (p ∧ q) ↔ ¬ p ∨ ¬ q :=
⟨not_and_of_not_or_not,not_or_not_of_not_and⟩

lemma not_not_iff_self {p : Prop} : ¬ ¬ p ↔ p :=
begin
  split ,
  { intro hnnp,
    cases classical.em p with h h,
    apply h, cases hnnp h },
  exact not_not_intro
end


-- lemma or_iff_or_imp_not (p q : Prop) : p ∨ q ↔ p ∨ (¬ p ∧ q) :=
-- sorry
