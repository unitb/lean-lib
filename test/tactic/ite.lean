import util.meta.tactic

example (x y : ℕ)
  (h : x ≤ 7)
  (h' : y ≤ 7)
: (if x ≤ y then x else y) ≤ 7 :=
begin
  ite_cases with h₃,
  all_goals { assumption }
end

example (x y : ℕ)
  (h : x ≤ 7)
  (h' : y ≤ 7)
: (if h'' : x ≤ y then x else y) ≤ 7 :=
begin
  ite_cases with h₃,
  all_goals { assumption }
end

example (x y i j : ℕ)
  (h : x ≤ i)
  (h' : y ≤ j)
: (if h : x ≤ y then x else y) ≤ (if x ≤ y then i else j) :=
begin
  ite_cases with h₃,
  all_goals { assumption }
end

example (x y i j : ℕ)
  (h : x ≤ i)
  (h' : y ≤ j)
: (if x ≤ y then x else y) ≤ if (if x ≤ y then tt else ff) then i else j :=
begin
  ite_cases with h₃,
  all_goals { assumption }
end

example (x y i j : ℕ)
  (f : ℕ → ℕ)
  (h'' : (if h : x ≤ y then x ≤ i else y ≤ j))
  (h''' : f (if h : x ≤ y then y else x) ≤ 7)
  (h'''' : (if h : x ≤ y then y else x) ≤ 7)
: (if h : x ≤ y then x else y) ≤ (if x ≤ y then i else j) :=
begin
  ite_cases with h₃ at ⊢ h'' h''',
  all_goals { assumption }
end

example (x y i j : ℕ)
  (f : ℕ → ℕ)
  (h'' : (if h : x ≤ y then x ≤ i else y ≤ j))
  (h''' : f (if h : x ≤ y then y else x) ≤ 7)
  (h'''' : (if h : x ≤ y then y else x) ≤ 7)
: x ≤ i ∨ y ≤ j :=
begin
  ite_cases with h₃ at ⊢ h'' h'''
  ; [ right , left ]
  ; assumption
end
