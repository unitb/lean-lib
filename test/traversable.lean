import category.traversable.derive category.traversable.instances

@[derive traversable]
inductive foo_bar (α : Type) : Type
 | left : α → foo_bar
 | right : list α → foo_bar

@[derive traversable]
structure my_struct (α β : Type) : Type :=
  (field1 : α)
  (field2 : list α)
  (other : ℕ)
  (field3 : β)

@[derive traversable]
inductive my_list  (α β : Type) : Type
 | last : α → my_list
 | cons : β → my_list → my_list

open function functor

example : traverse some { my_struct . field1 := [], field2 := [[],[7]]
                        , other := 4, field3 := 7 }
= some ({ my_struct . field1 := [], field2 := [[],[7]]
        , other := 4, field3 := 7 } : my_struct (list ℤ) ℕ) :=
by refl
