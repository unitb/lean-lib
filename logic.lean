
universe variables u u' u₀ u₁ u₂

lemma forall_imp_forall {α : Sort u} {p q : α → Prop}
   (h : ∀ a, (p a → q a))
   (p : ∀ a, p a) : ∀ a, q a :=
  take a, h _ (p a)

lemma forall_imp_forall' {α : Sort u} {β : Sort u'}
   {p : α → Prop}
   {q : β → Prop}
   (f : β → α)
   (h : ∀ a, (p (f a) → q a))
   (P : ∀ a, p a) : ∀ a, q a :=
begin
  intro a,
  apply h, apply P
end

lemma exists_imp_exists' {α : Sort u} {β : Sort u'}
   {p : α → Prop}
   {q : β → Prop}
   (f : α → β)
   (h : ∀ a, (p a → q (f a)))
   (P : ∃ a, p a) : ∃ a, q a :=
begin
  cases P with a P,
  exact ⟨_,h _ P⟩
end

lemma exists_imp_iff_forall_imp {α : Sort u}
  (p : α → Prop) (q : Prop)
: (∃ x, p x) → q ↔ (∀ x, p x → q) :=
begin
  split ; intros H,
  { intros x H',
    apply H _,
    exact ⟨_, H'⟩ },
  { intros H',
    cases H' with x H',
    apply H _ H', },
end

lemma exists_swap {α : Sort u} {β : Sort u'}
  (P : α → β → Prop)
: (∃ x y, P x y) ↔ (∃ y x, P x y) :=
begin
  split
  ; intros H
  ; cases H with x H
  ; cases H with y H
  ; exact ⟨_,_,H⟩
end

lemma forall_swap {α : Sort u} {β : Sort u'}
  (P : α → β → Prop)
: (∀ x y, P x y) ↔ (∀ y x, P x y) :=
begin
  split
  ; intros H x y
  ; apply H
end

lemma and_exists {α : Sort u}
   (P : Prop)
   (Q : α → Prop)
: P ∧ (∃ x, Q x) ↔ (∃ x, P ∧ Q x) :=
begin
  split
  ; intros H
  ; cases H with x H
  ; cases H with y H
  ; exact ⟨y,x,H⟩
end

lemma mem_set_of {α : Type u} (x : α) (P : α → Prop) : x ∈ set_of P ↔ P x :=
by refl

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

lemma assume_neg {p : Prop} : (¬ p → p) → p :=
begin
  intro h,
  cases classical.em p with h' h',
  { apply h' },
  { apply h h' },
end

lemma not_forall_iff_exists_not {t : Type u} (P : t → Prop)
: ¬ (∀ x, P x) ↔ (∃ x, ¬ P x) :=
begin
  split,
  { intro h, apply classical.by_contradiction, intros h',
    apply h, intro i,
    note h'' := forall_not_of_not_exists h' i,
    rw not_not_iff_self at h'',
    apply h'' },
  { intros h₀ h₁,
    cases h₀ with i h₀,
    apply h₀, apply h₁ },
end

lemma not_exists_iff_forall_not {t : Type u} (P : t → Prop)
: ¬ (∃ x, P x) ↔ (∀ x, ¬ P x) :=
begin
  split,
  { intros h x h',
    apply h,
    existsi x, apply h' },
  { intros h₀ h₁,
    cases h₁ with i h₁,
    apply h₀, apply h₁ },
end

lemma forall_or {t : Type u} (P Q R : t → Prop)
: (∀ x, P x ∨ Q x → R x) ↔ (∀ x, P x → R x) ∧ (∀ x, Q x → R x) :=
begin
  split ; intro h,
  split,
  all_goals { intros x h' },
  any_goals { cases h with h₀ h₁, cases h' with h₂ h₂ },
  { apply h, left, apply h' },
  { apply h, right, apply h'  },
  { apply h₀, apply h₂ },
  { apply h₁, apply h₂ },
end

lemma exists_option {t : Type u} (P : option t → Prop)
: (∃ x : option t, P x) ↔ P none ∨ ∃ x', P (some x') :=
begin
  split ; intro h,
  { cases h with x h,
    cases x with x,
    { left, assumption },
    { right, exact ⟨_,h⟩ } },
  { cases h with h h
    ; try { cases h with h h }
    ; exact ⟨_,h⟩ }
end

lemma exists_true (P : true → Prop)
: (∃ x : true, P x) ↔ P trivial :=
begin
  split ; intro h,
  { cases h with x h,
    cases x, apply h },
  { exact ⟨_,h⟩ }
end

lemma or_iff_not_imp (p q : Prop)
: p ∨ q ↔ ¬ p → q :=
sorry
