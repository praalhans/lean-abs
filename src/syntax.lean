-- (C) Copyright 2019, Hans-Dieter Hiep

import data.finmap data.bool

variables (α : Type) (β : Type)

-- Names have decidable equality.
class names := (deceq: decidable_eq α)

/-
We have the following class of dynamic names.
Given a finite set of names,
there can always be given a fresh instance not in that set.
(with thanks to Johannes Hölzl)
-/
class dynamic_names extends names α :=
(fresh: finset α → α)
(fresh_is_new: ∀x : finset α, (fresh x) ∉ x)

/-
Each program has global names.
Global names consist of a finite set of class names.
To each class name, there an associated finite set of field and method names.
-/
class global_names (α : Type) extends names α :=
(Nc: finset α)
(Nf (x : α) (H: x ∈ Nc): finset α)
(Nm (x : α) (H: x ∈ Nc): finset α)
open global_names

/-
A type in our object language is either:
a reference type (by class name),
a future of some type,
or a data type from the host language.
-/
inductive type [global_names α] : Type 1
| ref (x : α) (H: x ∈ Nc α): type
--| future: type -> type
| data: Type -> type

def type.void [global_names α] : type α := type.data α unit

open type

/-
A program signature consists of:
a map from class names to class declarations, and
a class name of the root object.

A class declaration (of some class self) consists of:
a map from self's field names to types, and
a map from self's method names to method declarations.

A method declaration consists of:
a return type and a list of types of its parameters.
-/

structure mdecl [global_names α] : Type 1 :=
(retype : type α)
(fparam : list (type α))

structure cdecl [global_names α] (self : α) (H: self ∈ Nc α) : Type 1 :=
(Mf (x : α) (H: x ∈ Nf self H) : type α)
(Mm (x : α) (H: x ∈ Nm self H) : mdecl α)

structure signature [global_names α] : Type 1 :=
(Mc (x : α) (H: x ∈ Nc α): cdecl α x H)
(main (x : α): x ∈ Nc α)

/-
We treat objects transparently.
Each object is associated to a single class name.
Given a set of objects, we can always construct some new object.
-/
class objects [global_names α] :=
(classof: β → {x // x ∈ Nc α})
(new: finset β → β)
(new_is_new: ∀x : finset β, (new x) ∉ x)

def objects.refof [global_names α] [objects α β] (o : β) : type α :=
    let i := objects.classof α o in ref i.val i.property

open objects

/-
We treat values as being of a type.
A value of a reference type is an object of the same class.
A value of a data type is a term of the type in the host language.
-/
inductive value [global_names α] [objects α β] : type α → Type 1
| obj (o : β) : value (refof α β o)
| term {γ : Type} (o : γ) : value (data α γ)
