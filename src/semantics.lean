-- (C) Copyright 2019, Hans-Dieter Hiep

import syntax

universes u
variables (α : Type) (β : Type)

open type

/-
We treat objects transparently.
Each object is associated to a single class name.
Given a set of objects, we can always construct some new object.
-/
class objects [global_names α] :=
(class_of: β → class_name α)
(new: finset β → β)
(new_is_new: ∀x : finset β, (new x) ∉ x)

def objects.type_of [global_names α] [objects α β] (o : β) : type α :=
    ref (objects.class_of α o)

open objects

/-
We treat values as being of a type.
A value of a reference type is an object of the same class.
A value of a data type is a term of the type in the host language.
-/
inductive value [global_names α] [objects α β] : type α → Type 1
| obj (o : β) : value (type_of α β o)
| term {γ : Type} (o : γ) : value (data α γ)