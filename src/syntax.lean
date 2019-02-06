-- (C) Copyright 2019, Hans-Dieter Hiep

import data.finmap data.bool data.vector data.list

universes u
variables (α : Type)

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

structure class_name [global_names α] :=
(name : α) (H : name ∈ Nc α)

structure field_name {α : Type} [global_names α] (self : class_name α) :=
(name : α) (H: name ∈ Nf self.name self.H)

structure method_name {α : Type} [global_names α] (self : class_name α) :=
(name : α) (H: name ∈ Nm self.name self.H)

/-
A type in our object language is either:
a reference type (by class name),
a future of some type,
or a data type from the host language.
-/
inductive type [global_names α] : Type 1
| ref: class_name α → type
--| future: type → type
| data: Type → type

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

structure cdecl {α : Type} [global_names α] (self : class_name α) : Type 1 :=
(fdecl : field_name self → type α)
(mdecl : method_name self → mdecl α)

structure signature [global_names α] : Type 1 :=
(cdecl (x : class_name α): cdecl x)
(main: class_name α)

def signature.method_params {α : Type} [global_names α] (sig : signature α)
{self : class_name α} (m : method_name self) : context α :=
    ((sig.cdecl self).mdecl m).fparam

def signature.return_type {α : Type} [global_names α] (sig : signature α)
{self : class_name α} (m : method_name self) : type α :=
    ((sig.cdecl self).mdecl m).retype

def signature.field_type {α : Type} [global_names α] (sig : signature α)
{self : class_name α} (f : field_name self) : type α :=
    (sig.cdecl self).fdecl f

/-
A field reference witnesses that a field
has a type in a given signature.
-/
def fieldref {α : Type} [global_names α] (sig : signature α)
{self : class_name α} (f : field_name self) (ty : type α) : Prop :=
    ty = sig.field_type f

/-
We consider type environments to consist of:
a signature,
a return type,
a method reference, and
declared local variables.
-/
structure tenv [global_names α] : Type 1 :=
(sig : signature α)
(self : class_name α)
(current : method_name self)
(locals : context α)

-- We introduce a non-Prop ∈ that contains position witness
inductive list_at {α : Type u} : α → list α → Type u
| head (x : α) (xs : list α): list_at x (x :: xs)
| tail (x y : α) (l : list α): list_at x l → list_at x (y :: l)

lemma list_at_mem (x : α) (l : list α) : list_at x l → x ∈ l :=
begin
    intro H,
    induction l,
    cases H,
    cases H,
    constructor, refl,
    have: x ∈ l_tl,
        apply l_ih, assumption,
    right, assumption
end

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

structure pvar {α : Type} [global_names α] (e : tenv α)
(ty : type α) : Type 1 :=
(idx : list_at ty (e.sig.method_params e.current))

structure lvar {α : Type} [global_names α] (e : tenv α)
(ty : type α) : Type 1 :=
(idx : list_at ty e.locals)

structure fvar {α : Type} [global_names α] (e : tenv α)
(ty : type α) : Type 1 :=
(field : field_name e.self)
(H : fieldref e.sig field ty)

def svar {α : Type} [global_names α] (e : tenv α)
(ty : type α) : Type 1 :=
    (lvar e ty) ⊕ (fvar e ty)

def rvar {α : Type} [global_names α] (e : tenv α)
(ty : type α) : Type 1 :=
    (pvar e ty) ⊕ (lvar e ty) ⊕ (fvar e ty)

/-
Given a method reference and a signature,
we have an argument list of variables with matching types.
Argument lists are constructed inductively over lists of types.
-/
inductive arglist {α : Type} [global_names α] (e : tenv α) :
list (type α) → Type 1
| nil : arglist []
| cons (x : type α) (xs : list (type α)) :
    rvar e x → arglist xs → arglist (x::xs)

/-
A pure expression evaluates to a value of a particular type.
-/

structure pure {α : Type} [global_names α] (e : tenv α) (t : type α) : Type 1 :=
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
inductive stmt {α : Type} [global_names α] (e : tenv α) : Type 1
| skip: stmt
| seq: stmt → stmt → stmt
| ite: pure e bool → stmt → stmt → stmt
| while: pure e bool → stmt → stmt
-- store in l the value of expr
| assign {ty : type α} (l : svar e ty): pure e ty → stmt
-- call method m, on object in r, with args τ
| async (c : class_name α) (r : rvar e (ref c))
    (m : method_name c) (τ : arglist e (e.sig.method_params m)): stmt
-- allocate new object of class c and store in l
| alloc (c : class_name α) (l : svar e (ref c)): stmt

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

structure pblock {α : Type} [global_names α]
(sig : signature α) {self : class_name α} (m : method_name self) : Type 1 :=
(locals : context α)
(S : stmt (tenv.mk sig self m locals))
(return : pure (tenv.mk sig self m locals) (sig.return_type m))

structure program {α : Type} [global_names α] (sig : signature α) : Type 1 :=
(body (self : class_name α) (m : method_name self): pblock sig m)
