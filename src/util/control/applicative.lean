
import util.data.functor

universe variables u v w u' v' w'

attribute [norm] seq_assoc pure_seq_eq_map map_pure

class applicative_pair (f : Type u → Type v) (g : Type u' → Type v') extends functor_pair f g :=
 (f_appl : applicative f)
 (g_appl : applicative g)
 (map_pure_comm : ∀ {α β}
            (hp : α → β)
            (x : α),
    map hp (pure x) = pure (hp x))
 (map_seq_comm : ∀ {α β : Type u} {α' β' : Type u'}
            (h : β → β')
            (hx : (α → β) → (α' → β'))
            (hy : α → α')
            (x : f (α → β))
            (y : f α),
    (∀ F y, hx F (hy y) = h (F y)) →
    map h (x <*> y) = map hx x <*> map hy y)

section lemmas

variables {α β γ : Type u}
variables {f : Type u → Type v}
variables [applicative f] [is_lawful_applicative f]

open function applicative is_lawful_applicative

section

variables (g : β → γ)
variables (x : f (α → β)) (y : f α)

lemma  applicative.map_seq_assoc
: @functor.map f _ _ _ g (x <*> y) = comp g <$> x <*> y :=
by rw [← pure_seq_eq_map
      ,seq_assoc
      ,map_pure
      ,pure_seq_eq_map]

end

section

open is_lawful_functor

variables (g : α → β)
variables (x : f (β → γ)) (y : f α)

lemma applicative.seq_map_comm
: x <*> g <$> y = flip comp g <$> x <*> y :=
begin
  rw [← pure_seq_eq_map _ y,seq_assoc,seq_pure,← comp_map],
  refl,
end

-- lemma d
-- : (has_seq.seq ∘ functor.map comp : f (α → β) → f (γ → α) → f (γ → β)) = _ :=
-- begin
--   apply funext, intro x,
--   apply funext, intro y,
--   unfold comp functor.map,
--   rw [← right_id comp,functor.map_comp],
-- end

end

@[norm]
lemma map_seq {β γ σ : Type u} (h : γ → σ) (x : f (β → γ)) (y : f β) :
  h <$> (x <*> y) = (comp h <$> x) <*> y :=
by rw [← pure_seq_eq_map,← pure_seq_eq_map
     ,seq_assoc
     ,map_pure]

@[norm]
lemma seq_map {β γ σ : Type u} (h : σ → β) (x : f (β → γ)) (y : f σ) :
  x <*> (h <$> y) = (flip comp h) <$> x <*> y :=
begin
  rw [← pure_seq_eq_map,← pure_seq_eq_map,seq_assoc] ,
  simp with norm,refl
end

end lemmas

/- identity applicative instance -/

namespace identity

open function

variables {α : Type u} {β : Type v} {γ : Type u'}

def pure : α → identity α := identity.mk

def seq : identity (α → β) → identity α → identity β
  | ⟨ f ⟩ ⟨ x ⟩ := ⟨ f x ⟩

local infix <$> := map
local infix <*> := seq

protected lemma pure_seq_eq_map (g : α → β) : ∀ (x : identity α), pure g <*> x = g <$> x
  | ⟨ x ⟩ := rfl

protected lemma map_pure (g : α → β) (x : α)
: g <$> pure x = pure (g x) :=
rfl

protected lemma seq_pure : ∀ (g : identity (α → β)) (x : α),
  g <*> pure x = (λ g : α → β, g x) <$> g
  | ⟨ g ⟩ x := rfl

protected lemma seq_assoc : ∀ (x : identity α) (g : identity (α → β)) (h : identity (β → γ)),
  h <*> (g <*> x) = (@comp α β γ <$> h) <*> g <*> x
| ⟨ x ⟩ ⟨ g ⟩ ⟨ h ⟩ := rfl

end identity

instance applicative_identity : applicative identity :=
{ map := @identity.map
, seq := @identity.seq
, pure := @identity.pure }

instance lawful_applicative_identity : is_lawful_applicative identity :=
{ id_map := @identity.id_map
, pure_seq_eq_map := @identity.pure_seq_eq_map
, map_pure := @identity.map_pure
, seq_pure := @identity.seq_pure
, seq_assoc := @identity.seq_assoc }

@[norm]
lemma identity.mk_eq_pure {α : Type v} (x : α)
: identity.mk x = pure x := rfl

lemma identity.seq_mk {α β : Type v}  (f : α → β) (x : α)
: identity.mk f <*> identity.mk x = identity.mk (f x) := rfl

instance : applicative_pair identity identity :=
{ (by apply_instance : functor_pair identity identity) with
  f_appl := by apply_instance
, g_appl := by apply_instance
, map_pure_comm :=
  by { intros, refl }
, map_seq_comm :=
  begin
    intros α β α' β',
    intros h hx hy x y H,
    cases x with x,
    cases y with y,
    unfold has_seq.seq identity.seq functor_pair.map identity.map,
    rw H,
  end }

/- compose applicative instance -/

namespace compose

open function is_lawful_functor is_lawful_applicative

section applicative

variables {f : Type u → Type u'} {g : Type v → Type u}

variables [applicative f] [applicative g]
section
variables {α β γ : Type v}

def seq : compose f g (α → β) → compose f g α → compose f g β
  | ⟨ h ⟩ ⟨ x ⟩ := ⟨ has_seq.seq <$> h <*> x ⟩

def pure : α → compose f g α := compose.mk ∘ has_pure.pure ∘ has_pure.pure
end

variables [is_lawful_applicative f] [is_lawful_applicative g]
variables {α β γ : Type v}

local infix ` <$> ` := map
local infix ` <*> ` := seq

protected lemma map_pure (h : α → β) (x : α) : (h <$> pure x : compose f g β) = pure (h x) :=
begin
  unfold compose.pure comp compose.map,
  apply congr_arg,
  rw [map_pure,map_pure],
end

protected lemma seq_pure (h : compose f g (α → β)) (x : α)
: h <*> pure x = (λ g : α → β, g x) <$> h :=
begin
  cases h with h,
  simp!  with norm,
  apply congr_fun, apply congr_arg, funext,
  simp with norm,
end

protected lemma seq_assoc : ∀ (x : compose f g α) (h₀ : compose f g (α → β)) (h₁ : compose f g (β → γ)),
   h₁ <*> (h₀ <*> x) = (@comp α β γ <$> h₁) <*> h₀ <*> x
| ⟨ x ⟩ ⟨ h₀ ⟩ ⟨ h₁ ⟩ :=
by { simp! [comp,flip] with norm, }

lemma pure_seq_eq_map (h : α → β) : ∀ (x : compose f g α), pure h <*> x = h <$> x
  | ⟨ x ⟩ :=
begin
  simp!  with norm,
  congr, funext, simp with norm,
end

end applicative

end compose

instance applicative_compose
  {f : Type u → Type u'} {g : Type v → Type u}
  [applicative f] [applicative g]
: applicative (compose f g) :=
{ map := @compose.map f g _ _
, seq := @compose.seq f g _ _
, pure := @compose.pure f g _ _ }

instance lawful_applicative_compose
  {f : Type u → Type u'} {g : Type v → Type u}
  [applicative f] [applicative g]
  [is_lawful_applicative f] [is_lawful_applicative g]
: is_lawful_applicative (compose f g) :=
{ id_map := @is_lawful_functor.id_map _ _ _
, comp_map := @is_lawful_functor.comp_map _ _ _
, pure_seq_eq_map := @compose.pure_seq_eq_map f g _ _ _ _
, map_pure := @compose.map_pure f g _ _ _ _
, seq_pure := @compose.seq_pure f g _ _ _ _
, seq_assoc := @compose.seq_assoc f g _ _ _ _ }

@[norm]
lemma compose.seq_mk {α β : Type u'}
  {f : Type u → Type v} {g : Type u' → Type u}
  [applicative f] [applicative g]
  (h : f (g (α → β))) (x : f (g α))
: compose.mk h <*> compose.mk x = compose.mk (has_seq.seq <$> h <*> x) := rfl

namespace compose

section applicative_pair

parameters {f :  Type v  → Type w}  {g  : Type u  → Type v}
parameters {f' : Type v' → Type w'} {g' : Type u' → Type v'}
parameters [applicative_pair f f'] [applicative_pair g g']
parameters {α β : Type u} {α' β' : Type u'}

instance applicative_f : applicative f := applicative_pair.f_appl f f'
instance applicative_g : applicative g := applicative_pair.f_appl g g'
instance applicative_f' : applicative f' := applicative_pair.g_appl f f'
instance applicative_g' : applicative g' := applicative_pair.g_appl g g'

lemma map_pure_comm (hp : α → β') (x : α)
:   functor_pair.map (compose f' g') hp (compose.pure x : compose f g α)
  = compose.pure (hp x) :=
begin
  unfold compose.pure function.comp functor_pair.map map_pair,
  apply congr_arg,
  rw applicative_pair.map_pure_comm,
  rw applicative_pair.map_pure_comm,
end

lemma map_seq_comm (h : β → β') (hx : (α → β) → α' → β') (hy : α → α')
                   (x : compose f g (α → β)) (y : compose f g α)
                   (H : ∀ (F : α → β) (y : α), hx F (hy y) = h (F y))
:   functor_pair.map (compose f' g') h (x <*> y)
  = functor_pair.map (compose f' g') hx x <*> functor_pair.map (compose f' g') hy y  :=
begin
  cases x with x,
  cases y with y,
  unfold has_seq.seq compose.seq functor_pair.map map_pair,
  apply congr_arg,
  let x' : f (g α → g β) := functor.map has_seq.seq x,
  let h' : g β → g' β' := (functor_pair.map g' h),
  let hx' : (g α → g β) → g' α' → g' β' := λ F i, functor_pair.map _ h (F sorry),
  let hy' : g α → g' α' := functor_pair.map _ hy,
  let hh := @functor_pair.map g g' _ _ _ h,
  have H' : (∀ (F : g α → g β) (y : g α), hx' F (hy' y) = h' (F y)) := sorry,
  rw @applicative_pair.map_seq_comm f f' _ (g α) (g β) (g' α') (g' β')
        h' hx' hy' x' y H',
  admit,
end

end applicative_pair

end compose

instance
  {f :  Type v  → Type w}  {g  : Type u  → Type v}
  {f' : Type v' → Type w'} {g' : Type u' → Type v'}
  [applicative_pair f f'] [applicative_pair g g']
: applicative_pair (compose f g) (compose f' g') :=
{ (by apply_instance : functor_pair (compose f g) (compose f' g')) with
  f_appl := by apply applicative_compose
, g_appl := by apply applicative_compose
, map_pure_comm := @compose.map_pure_comm f g f' g' _ _
, map_seq_comm := @compose.map_seq_comm f g f' g' _ _ }

namespace applicative

def lift {m : Type u → Type v} [functor m] {α φ : Type u} (f : α → φ) (ma : m α) : m φ :=
f <$> ma

variables {m : Type u → Type v} [applicative m]
def lift₂
  {α₁ α₂ φ : Type u}
  (f : α₁ → α₂ → φ)
  (ma₁ : m α₁) (ma₂: m α₂) : m φ :=
f <$> ma₁ <*> ma₂

def mmap₂
  {α₁ α₂ φ : Type u}
  (f : α₁ → α₂ → m φ)
: Π (ma₁ : list α₁) (ma₂: list α₂), m (list φ)
 | (x :: xs) (y :: ys) := (::) <$> f x y <*> mmap₂ xs ys
 | _ _ := pure []


def lift₃
  {α₁ α₂ α₃ φ : Type u}
  (f : α₁ → α₂ → α₃ → φ)
  (ma₁ : m α₁) (ma₂: m α₂) (ma₃ : m α₃) : m φ :=
f <$> ma₁ <*> ma₂ <*> ma₃

def lift₄
  {α₁ α₂ α₃ α₄ φ : Type u}
  (f : α₁ → α₂ → α₃ → α₄ → φ)
  (ma₁ : m α₁) (ma₂: m α₂) (ma₃ : m α₃) (ma₄ : m α₄) : m φ :=
f <$> ma₁ <*> ma₂ <*> ma₃ <*> ma₄

def lift₅
  {α₁ α₂ α₃ α₄ α₅ φ : Type u}
  (f : α₁ → α₂ → α₃ → α₄ → α₅ → φ)
  (ma₁ : m α₁) (ma₂: m α₂) (ma₃ : m α₃) (ma₄ : m α₄) (ma₅ : m α₅) : m φ :=
f <$> ma₁ <*> ma₂ <*> ma₃ <*> ma₄ <*> ma₅

open nat
variables {α : Type u}
variables {β : Type v}
variables {γ : Type w}

def replicate : ℕ → m α → m (list α)
 | 0 _ := pure []
 | (succ n) m := (::) <$> m <*> replicate n m

def replicate' : ℕ → m α → m punit
 | 0 _ := pure punit.star
 | (succ n) m := m *> replicate' n m

def mapp (f : γ → β → α) : list (γ × β) → list α
 | [ ] := [ ]
 | ((x,y) :: xs) := f x y :: mapp xs

def mmapp (f : γ → β → m α) : list (γ × β) → m (list α)
 | [ ] := pure [ ]
 | ((x,y) :: xs) := (::) <$> f x y <*> mmapp xs

def mmapp' (f : γ → β → m α) : list (γ × β) → m punit
 | [ ] := pure punit.star
 | ((x,y) :: xs) := f x y *> mmapp' xs

end applicative
