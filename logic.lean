
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
