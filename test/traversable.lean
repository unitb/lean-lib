import util.data.traversable

inductive foo_bar (α : Type) : Type
 | left : α → foo_bar
 | right : list α → foo_bar

structure my_struct (α β : Type) : Type :=
  (field1 : α)
  (field2 : list α)
  (other : ℕ)
  (field3 : β)

inductive my_list  (α β : Type) : Type
 | last : α → my_list
 | cons : β → my_list → my_list

instance {β : Type} : has_traverse (my_struct β) :=
by { derive_traverse, }

instance : has_traverse foo_bar :=
by { derive_traverse, }

instance {β : Type} : has_traverse (my_list β) :=
by { derive_traverse }

open function functor

example : traverse some (my_list.cons 3 (my_list.cons 7 (my_list.last _ 21)))
= some (my_list.cons 3 (my_list.cons 7 (my_list.last _ 21))) :=
by refl

example : traverse some { my_struct . field1 := [], field2 := [[],[7]]
                        , other := 4, field3 := 7 }
= some ({ my_struct . field1 := [], field2 := [[],[7]]
        , other := 4, field3 := 7 } : my_struct (list ℤ) ℕ) :=
by refl
