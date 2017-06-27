
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

lemma exists_or  {α : Type u}
   {p q : α → Prop}
: (∃ i, p i ∨ q i) ↔ (∃ i, p i) ∨ (∃ i, q i) :=
begin
  split ; intro h,
  { cases h with i h,
    apply or.imp _ _ h
    ; apply exists.intro },
  { cases h with h h
    ; revert h
    ; apply exists_imp_exists
    ; intro,
    { apply or.intro_left },
    { apply or.intro_right }, },
end

lemma exists_imp_exists'' {α : Sort u} {β : Sort u'}
   {p : α → Prop}
   {q : β → Prop}
   (f : ∀ x: α, p x → β)
   (h : ∀ a (h : p a), q (f a h))
   (P : ∃ a, p a) : ∃ a, q a :=
begin
  cases P with a P,
  existsi f a P,
  apply h _ P,
end

lemma exists_imp_exists' {α : Sort u} {β : Sort u'}
   {p : α → Prop}
   {q : β → Prop}
   (f : α → β)
   (h : ∀ a, p a → q (f a))
   (P : ∃ a, p a) : ∃ a, q a :=
begin
  cases P with a P,
  existsi f a,
  apply h _ P,
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

lemma exists_and {α : Sort u}
   (P : α → Prop)
   (Q : Prop)
: (∃ x, P x) ∧ Q ↔ (∃ x, P x ∧ Q) :=
by simp [and_exists]

lemma mem_set_of {α : Type u} (x : α) (P : α → Prop) : x ∈ set_of P ↔ P x :=
by refl

lemma and.imp_left {p p' q : Prop}
  (hp : p → p')
: p ∧ q → p' ∧ q := and.imp hp id

lemma and.imp_right {p q q' : Prop}
  (hp : q → q')
: p ∧ q → p ∧ q' := and.imp id hp

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

lemma iff_of_not_iff_not {p q : Prop} (h : ¬ p ↔ ¬ q)
: p ↔ q :=
begin
  split ; intro h₀ ; apply classical.by_contradiction,
  { rw -h, intro h₁, apply h₁ h₀ },
  { rw h, intro h₁, apply h₁ h₀ },
end

lemma not_iff_not_iff {p q : Prop}
: (¬ p ↔ ¬ q) ↔ (p ↔ q) :=
⟨ iff_of_not_iff_not, not_congr ⟩

lemma distrib_right_or
: c ∨ (a ∧ b) ↔ (c ∨ a) ∧ (c ∨ b) :=
by { rw [or_comm,distrib_left_or], simp }

lemma or_not_and (p q : Prop)
: p ∨ (¬ p ∧ q) ↔ p ∨ q :=
by simp [distrib_right_or,iff_true_intro $ classical.em p]

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

lemma and_shunting (p q r : Prop)
: (p ∧ q → r) ↔ (p → q → r) :=
begin
  split ; intro h,
  { intros hp hq,
    apply h ⟨hp,hq⟩ },
  { intro h', cases h' with hp hq,
    apply h hp hq }
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
    have h'' := forall_not_of_not_exists h' i,
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

lemma true_imp (p : Prop)
: true → p ↔ p :=
by { split ; intro h ; intros ; apply h ; trivial }

lemma distrib_left_and (p q r : Prop)
: p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  cases classical.em p with h h,
  { simp [eq_true_intro h] },
  { simp [eq_false_intro h] },
end

lemma or_iff_not_imp (p q : Prop)
: p ∨ q ↔ ¬ p → q :=
begin
  cases classical.em p with hp hnp,
  { rw [eq_true_intro hp,true_or,not_true,false_implies_iff], },
  { rw [eq_false_intro hnp,false_or,not_false_iff,true_imp], }
end

lemma imp_iff_not_or (p q : Prop)
: p → q ↔ ¬ p ∨ q :=
by rw [or_iff_not_imp,not_not_iff_self]

lemma exists_one_point_right {α : Type u} (y : α) {p : α → Prop}
  (h : ∀ x, p x → x = y)
: (∃ x, p x) ↔ p y :=
begin
  split ; intro h,
  { cases h with x h',
    rw [-h _ h'],
    apply h' },
  { exact ⟨_,h⟩ }
end

lemma exists_variable_change' {α : Type u} {β : Type u'}
  (p : α → Prop) (q : β → Prop)
  (f : ∀ x : α, p x → β) (g : ∀ x : β, q x → α)
  (Hf : ∀ x (h: p x), q (f x h))
  (Hg : ∀ x (h: q x), p (g x h))
: (∃ i, p i) ↔ (∃ j, q j) :=
begin
  split,
  { apply exists_imp_exists'' f Hf, },
  { apply exists_imp_exists'' g Hg, },
end

lemma exists_variable_change {α : Type u} {β : Type u'}
  (p : α → Prop) (q : β → Prop)
  (f : α → β) (g : β → α)
  (Hf : ∀ x, p x → q (f x))
  (Hg : ∀ x, q x → p (g x))
: (∃ i, p i) ↔ (∃ j, q j) :=
begin
  apply exists_variable_change' p q (λ x (h : p x), f x)  (λ x (h : q x), g x),
  apply Hf,
  apply Hg,
end

lemma exists_range_subtype {α : Type u}
  (p : α → Prop) (q : α → Prop)
: (∃ i, p i ∧ q i) ↔ (∃ j : subtype p, q j) :=
begin
  let f := λ (x : α) (h : p x ∧ q x), subtype.mk x h.left,
  let g := λ (x : subtype p) (h : q x), x.val,
  apply exists_variable_change' _ _ f g,
  { intros x h, apply h.right },
  { intros x h, exact ⟨x.property, h⟩  },
end

lemma or_of_ite {c t f : Prop} [decidable c]
  (h : ite c t f)
: (c ∧ t) ∨ (¬ c ∧ f) :=
begin
  cases decidable.em c with hc hnc,
  { left,
    rw [if_pos hc] at h,
    exact ⟨hc,h⟩ },
  { right,
    rw [if_neg hnc] at h,
    exact ⟨hnc,h⟩ },
end

lemma or_of_ite' {c t f : Prop} [decidable c]
  (h : ite c t f)
: t ∨ f :=
begin
  apply or.imp _ _ (or_of_ite h)
  ; apply and.right
end

def rtc {α : Type u} (r : α → α → Prop) (x y : α) := x = y ∨ tc r x y

@[refl]
def rtc_refl {α : Type u} {r : α → α → Prop} {x : α}
: rtc r x x :=
begin
  unfold rtc,
  left, refl
end

@[trans]
def rtc_trans {α : Type u} {r : α → α → Prop} {x : α} (y : α) {z : α}
  (h₀ : rtc r x y)
  (h₁ : rtc r y z)
: rtc r x z :=
begin
  unfold rtc at h₀,
  cases h₀ with h₀ h₀,
  { subst y, apply h₁ },
  unfold rtc at h₁,
  cases h₁ with h₁ h₁,
  { subst z, apply or.intro_right _ h₀ },
  { apply or.intro_right,
    apply tc.trans _ _ _ h₀ h₁, }
end
