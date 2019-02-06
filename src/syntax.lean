-- (C) Copyright 2019, Hans-Dieter Hiep

import data.finmap data.bool data.vector data.list

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

instance Type_to_type [global_names α] : has_coe Type (type α) :=
    ⟨type.data α⟩

def type.void [global_names α] : type α := type.data α unit

open type

/-
A variable context is a list of types;
we employ De Bruijn encoding for indexing in this context.
-/
@[reducible]
def context [global_names α] : Type 1 := list (type α)

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
(fparam : context α)

structure cdecl [global_names α] (self : α) (H: self ∈ Nc α) : Type 1 :=
(Mf (x : α) (H: x ∈ Nf self H) : type α)
(Mm (x : α) (H: x ∈ Nm self H) : mdecl α)

structure signature [global_names α] : Type 1 :=
(Mc (x : α) (H: x ∈ Nc α): cdecl α x H)
(main (x : α): x ∈ Nc α)

/-
A method is a particular path within a signature.
Given a method, we know its enclosing class name.
-/
structure method [global_names α] : Type 1 :=
(sig : signature α) (self : α) (m : α) (H: self ∈ Nc α) (G: m ∈ Nm self H)

def method.fparam [global_names α] (m : method α) : context α :=
    ((m.sig.Mc m.self m.H).Mm m.m m.G).fparam
def method.retype [global_names α] (m : method α) : type α :=
    ((m.sig.Mc m.self m.H).Mm m.m m.G).retype
def method.thtype [global_names α] (m : method α) : type α :=
    ref m.self m.H

/-
We consider typing environments to consist of:
a method, and
a context of local variables.

Within a typing environment, we refer to numerous things.
An argument refers to the
type and its index within the formal parameters of its method.
A local variable refers to the
type and its index within the context of local variables.
A variable refers to either an argument or a local variable.
A fieldref refers to a field within the enclosed class.
-/

structure tenv [global_names α] : Type 1 :=
(method : method α)
(locals : context α)

-- TODO: replace ∈ by non-Prop at type, that contains info on position

structure arg [global_names α] (e : tenv α) : Type 1 :=
(type : type α) (idx : type ∈ e.method.fparam α)

structure lvar [global_names α] (e : tenv α) : Type 1 :=
(type : type α) (idx : type ∈ e.locals)

def var [global_names α] (e : tenv α) : Type 1 := sum (arg α e) (lvar α e)

-- TODO: introduce variants of arg, lval and var that enforce a type

def var.type [global_names α] {e : tenv α} (v : var α e) : type α :=
sorry -- TODO

structure fieldref [global_names α] (e : tenv α) : Type 1 :=
(x : true) -- TODO

def fieldref.type [global_names α] {e : tenv α} (f : fieldref α e) : type α :=
sorry -- TODO

structure pure [global_names α] (e : tenv α) (t : type α) : Type 1 :=
(x : true) -- TODO

/-
A statement within a typing environment is either:
a skip,
a sequential composition,
a branch,
a loop,
a field assignment,
a local assignment,
an asynchronous method call,
an object allocation.
-/
inductive stmt [global_names α] (e : tenv α) : Type 1
| skip: stmt
| seq: stmt → stmt → stmt
| ite: pure α e bool → stmt → stmt → stmt
| while: pure α e bool → stmt → stmt
| set (f : fieldref α e): pure α e f.type → stmt
| set (l : lvar α e): pure α e l.type → stmt
| async (m : methodref α) (r : lvar' α m.thtype) (τ : arglist α e m)
    (l : lvar' α e m.retype): stmt
| alloc (c : classref α) (l : lvar' α c.type): stmt

/-
A program with a given program signature associates
to each method of each class a program block.

A program block associated to a method consists of:
local variable declarations,
a statement within a typing environment, and
a return of a pure expression within a typing environment.
The type of the pure expressions is the return type of the method.

A pure expression takes an assignment and produces a value of some type.
-/

structure pblock [global_names α] (m : mth α) : Type 1 :=
(flocal : context α)
(S : stmt α (tenv.mk m flocal))
(return : pure α (tenv.mk m flocal) m.retype)

structure program [global_names α] (sig : signature α) : Type 1 :=
(Mp (m : mth α): true)

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
