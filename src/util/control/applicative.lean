
import util.data.functor

universe variables u v w u' v' w'

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
variables [applicative f]

open function applicative

section

variables (g : β → γ)
variables (x : f (α → β)) (y : f α)

lemma applicative.map_seq_assoc
: @has_map.map f _ _ _ g (x <*> y) = comp g <$> x <*> y :=
by rw [← pure_seq_eq_map
      ,seq_assoc
      ,map_pure
      ,pure_seq_eq_map]

end

section

variables (g : α → β)
variables (x : f (β → γ)) (y : f α)

lemma applicative.seq_map_comm
: x <*> g <$> y = flip comp g <$> x <*> y :=
begin
  rw [← pure_seq_eq_map _ y,seq_assoc,seq_pure,← functor.map_comp],
  refl,
end

-- lemma d
-- : (has_seq.seq ∘ has_map.map comp : f (α → β) → f (γ → α) → f (γ → β)) = _ :=
-- begin
--   apply funext, intro x,
--   apply funext, intro y,
--   unfold comp has_map.map,
--   rw [← right_id comp,functor.map_comp],
-- end

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

lemma pure_seq_eq_map (g : α → β) : ∀ (x : identity α), pure g <*> x = g <$> x
  | ⟨ x ⟩ := rfl

lemma map_pure (g : α → β) (x : α)
: g <$> pure x = pure (g x) :=
rfl

lemma seq_pure : ∀ (g : identity (α → β)) (x : α),
  g <*> pure x = (λ g : α → β, g x) <$> g
  | ⟨ g ⟩ x := rfl

lemma seq_assoc : ∀ (x : identity α) (g : identity (α → β)) (h : identity (β → γ)),
  h <*> (g <*> x) = (@comp α β γ <$> h) <*> g <*> x
| ⟨ x ⟩ ⟨ g ⟩ ⟨ h ⟩ := rfl

end identity

instance applicative_identity : applicative identity :=
{ map := @identity.map
, id_map := @identity.id_map
, pure := @identity.pure
, seq := @identity.seq
, pure_seq_eq_map := @identity.pure_seq_eq_map
, map_pure := @identity.map_pure
, seq_pure := @identity.seq_pure
, seq_assoc := @identity.seq_assoc }

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

open function

section applicative

variables {f : Type u → Type u'} {g : Type v → Type u}

variables [applicative f] [applicative g]
variables {α β γ : Type v}

def seq : compose f g (α → β) → compose f g α → compose f g β
  | ⟨ h ⟩ ⟨ x ⟩ := ⟨ has_seq.seq <$> h <*> x ⟩

def pure : α → compose f g α := compose.mk ∘ has_pure.pure f ∘ has_pure.pure g

local infix ` <$> ` := map
local infix ` <*> ` := seq

lemma map_pure (h : α → β) (x : α) : (h <$> pure x : compose f g β) = pure (h x) :=
begin
  unfold compose.pure comp compose.map,
  apply congr_arg,
  rw [applicative.map_pure,applicative.map_pure],
end

lemma seq_pure (h : compose f g (α → β)) (x : α)
: h <*> pure x = (λ g : α → β, g x) <$> h :=
begin
  cases h with h,
  unfold compose.map compose.pure compose.seq comp,
  apply congr_arg,
  rw [applicative.seq_pure,← functor.map_comp],
  apply congr_fun, apply congr_arg,
  apply funext, intro y,
  unfold comp,
  apply applicative.seq_pure
end

lemma seq_assoc : ∀ (x : compose f g α) (h₀ : compose f g (α → β)) (h₁ : compose f g (β → γ)),
   h₁ <*> (h₀ <*> x) = (@comp α β γ <$> h₁) <*> h₀ <*> x
| ⟨ x ⟩ ⟨ h₀ ⟩ ⟨ h₁ ⟩ :=
begin
  unfold compose.seq compose.map,
  apply congr_arg,
  repeat { rw [applicative.seq_assoc] },
  apply congr_fun,
  apply congr_arg,
  rw [← functor.map_comp],
  rw [← functor.map_comp],
  rw [← applicative.pure_seq_eq_map has_seq.seq
     ,applicative.seq_assoc
     ,applicative.seq_pure _ has_seq.seq],
  repeat { rw [← functor.map_comp] },
  rw [applicative.map_seq_assoc has_seq.seq,← functor.map_comp],
  apply congr_fun,
  apply congr_arg,
  apply congr_fun,
  apply congr_arg,
  { apply funext, intro i,
    unfold comp,
    apply funext, intro j,
    apply funext, intro k,
    rw [applicative.seq_assoc] },
end

lemma pure_seq_eq_map (h : α → β) : ∀ (x : compose f g α), pure h <*> x = h <$> x
  | ⟨ x ⟩ :=
begin
  unfold compose.pure compose.seq compose.map comp,
  apply congr_arg,
  rw [applicative.map_pure,applicative.pure_seq_eq_map],
  apply congr_fun,
  apply congr_arg,
  apply funext, clear x, intro x,
  apply applicative.pure_seq_eq_map
end

end applicative

end compose

instance applicative_compose
  {f : Type u → Type u'} {g : Type v → Type u}
  [applicative f] [applicative g]
: applicative (compose f g) :=
{ map := @compose.map f g _ _
, id_map := @compose.id_map f g _ _
, map_comp := @compose.map_comp f g _ _
, seq := @compose.seq f g _ _
, pure := @compose.pure f g _ _
, pure_seq_eq_map := @compose.pure_seq_eq_map f g _ _
, map_pure := @compose.map_pure f g _ _
, seq_pure := @compose.seq_pure f g _ _
, seq_assoc := @compose.seq_assoc f g _ _ }

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
  let x' : f (g α → g β) := has_map.map has_seq.seq x,
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

lemma compose.seq_mk {α β : Type u'}
  {f : Type u → Type v} {g : Type u' → Type u}
  [applicative f] [applicative g]
  (h : f (g (α → β))) (x : f (g α))
: compose.mk h <*> compose.mk x = compose.mk (has_seq.seq <$> h <*> x) := rfl

namespace applicative

def lift {m : Type u → Type v} [functor m] {α φ : Type u} (f : α → φ) (ma : m α) : m φ :=
f <$> ma

variables {m : Type u → Type v} [applicative m]
def lift₂
  {α₁ α₂ φ : Type u}
  (f : α₁ → α₂ → φ)
  (ma₁ : m α₁) (ma₂: m α₂) : m φ :=
f <$> ma₁ <*> ma₂

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

def mmapp (f : γ → β → m α) : list (γ × β) → m (list α)
 | [ ] := pure [ ]
 | ((x,y) :: xs) := (::) <$> f x y <*> mmapp xs

end applicative
