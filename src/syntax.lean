-- (C) Copyright 2019, Hans-Dieter Hiep

import data.finmap data.bool data.vector data.list
import util

-- Names have decidable equality.
class names (α : Type) := [deceq: decidable_eq α]

/-
Each program has global names.
Global names consist of a finite set of class names.
To each class name, there an associated finite set of field and method names.
-/
class global_names (α : Type) extends names α :=
(Nc: finset α)
(Nf (x : α) (H: x ∈ Nc): finset α)
(Nm (x : α) (H: x ∈ Nc): finset α)

structure class_name (α : Type) [global_names α] :=
(name : α) (H : name ∈ global_names.Nc α)

structure field_name {α : Type} [global_names α] (self : class_name α) :=
(name : α) (H: name ∈ global_names.Nf self.name self.H)

structure method_name {α : Type} [global_names α] (self : class_name α) :=
(name : α) (H: name ∈ global_names.Nm self.name self.H)

/-
A type in our object language is either:
a reference type (by class name),
a future of some type,
or a data type from the host language.
-/
inductive type (α : Type) [global_names α] : Type 1
| ref: class_name α → type
--| future: type → type
| data: Type → type

instance Type_to_type (α : Type) [global_names α] : has_coe Type (type α) :=
    ⟨type.data α⟩

def type.void (α : Type) [global_names α] : type α := type.data α unit

open type

/-
A variable context is a list of types;
we employ De Bruijn encoding for indexing in this context.
-/
@[reducible]
def context (α : Type) [global_names α] : Type 1 := list (type α)

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

structure mdecl {α : Type} [global_names α]
{self : class_name α} (m : method_name self) : Type 1 :=
(retype : type α)
(fparam : context α)

structure fdecl {α : Type} [global_names α]
{self : class_name α} (f : field_name self) : Type 1 :=
(type : type α)

structure cdecl {α : Type} [global_names α] (self : class_name α) : Type 1 :=
(fdecl (f : field_name self) : fdecl f)
(mdecl (m : method_name self) : mdecl m)

class signature (α : Type) extends global_names α : Type 1 :=
(cdef (x : class_name α): cdecl x)
(main: class_name α)

def signature.method_params {α : Type} [signature α]
{self : class_name α} (m : method_name self) : context α :=
    ((signature.cdef self).mdecl m).fparam

def signature.return_type {α : Type} [signature α]
{self : class_name α} (m : method_name self) : type α :=
    ((signature.cdef self).mdecl m).retype

def signature.field_type {α : Type} [signature α]
{self : class_name α} (f : field_name self) : type α :=
    ((signature.cdef self).fdecl f).type

open signature

/-
Given a signature, we consider type environments to consist of:
a return type,
a method reference, and
declared local variables.
-/
structure tenv (α : Type) [signature α] : Type 1 :=
(self : class_name α)
(current : method_name self)
(locals : context α)

/-
A note on terminology.
Parameter: as declared in signature
Argument: as supplied in a method call
-/

/-
Within a typing environment, we refer to numerous things.
A parameter refers to the
index within the parameters of the current method.
A local refers to the
index within the declared local variables.
A field refers to a field within the enclosed class.
A variable refers to either an argument, a local, or a field.
-/

structure pvar {α : Type} [signature α] (e : tenv α)
(ty : type α) : Type 1 :=
(idx : list_at ty (method_params e.current))

structure lvar {α : Type} [signature α] (e : tenv α)
(ty : type α) : Type 1 :=
(idx : list_at ty e.locals)

structure fvar {α : Type} [signature α] (e : tenv α)
(ty : type α) : Type 1 :=
(idx : field_name e.self)
(H : ty = field_type idx)

-- Store variable (LHS only)
inductive svar {α : Type} [signature α] (e : tenv α)
(ty : type α) : Type 1
| fvar: fvar e ty → svar
| lvar: lvar e ty → svar

-- Read variable (RHS only)
inductive rvar {α : Type} [signature α] (e : tenv α)
(ty : type α) : Type 1
| fvar: fvar e ty → rvar
| pvar: pvar e ty → rvar
| lvar: lvar e ty → rvar

/-
Given a typing environment and a list of types,
we have an argument list of variables with matching types.
-/
inductive arglist {α : Type} [signature α] (e : tenv α) :
list (type α) → Type 1
| nil : arglist []
| cons (x : type α) (xs : list (type α)) :
    rvar e x → arglist xs → arglist (x::xs)

/-
A pure expression evaluates to a value of a particular type.
Such expressions are either:
a constant data value,
a function application on data values,
value lookup in environment,
referential equality check.
-/
inductive pexp {α : Type} [signature α] (e : tenv α) :
type α → Type 1
| const (γ : Type) : γ → pexp γ
| apply (γ δ : Type) : pexp (γ → δ) → pexp γ → pexp δ
| lookup {ty : type α} : rvar e ty → pexp ty
| requal (c : class_name α) : pexp (ref c) → pexp (ref c) → pexp bool

/-
A statement within a typing environment is either:
a skip,
a sequential composition,
a branch,
a loop,
an assignment,
an asynchronous method call,
an object allocation.
-/
inductive stmt {α : Type} [signature α] (e : tenv α) : Type 1
| skip: stmt
| seq: stmt → stmt → stmt
| ite: pexp e bool → stmt → stmt → stmt
| while: pexp e bool → stmt → stmt
-- store in l the value of expr
| assign {ty : type α} (l : svar e ty): pexp e ty → stmt
-- call method m, on object in r, with args τ
| async (c : class_name α) (r : rvar e (ref c))
    (m : method_name c) (τ : arglist e (method_params m)): stmt
-- allocate new object of class c and store reference in l
| alloc (c : class_name α) (l : svar e (ref c)): stmt

/-
A program with a given program signature associates
to each method of each class a program block.

A program block associated to a method consists of:
local variable declarations, and
a statement within a typing environment.
-/

structure pblock {α : Type} [signature α]
{self : class_name α} (m : method_name self) : Type 1 :=
(locals : context α)
(S : stmt (tenv.mk self m locals))

structure program {α : Type} [signature α] : Type 1 :=
(body {self : class_name α} (m : method_name self): pblock m)
