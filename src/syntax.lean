-- (C) Copyright 2019, Hans-Dieter Hiep

import data.finmap data.bool data.vector data.list
import util

/- Each program has names. Names consist of a finite set of class names. To each class name, there an associated finite set of field and method names. To each method name, there is an associated finite set of parameter names. -/
class names (α : Type) :=
(Nc: finset α)
(Nf {x : α} (H: x ∈ Nc): finset α)
(Nm {x : α} (H: x ∈ Nc): finset α)
(Np {x : α} {H: x ∈ Nc} {y : α} (G : y ∈ Nm H): finset α)
section open names variables {α : Type} [names α]
  structure class_name (α : Type) [names α] :=
    (name : α) (H : name ∈ Nc α)
  
  section variables (self : class_name α)
    structure field_name :=
      (name : α) (G: name ∈ Nf self.H)
    structure method_name :=
      (name : α) (G: name ∈ Nm self.H)
  end
  variable {self : class_name α}
  structure param_name (m : method_name self) :=
    (name : α) (F: name ∈ Np m.G)
end

/- A type in our object language is either: a reference type (by class name), or a data type from the host language. -/
section variables (α : Type) [names α]
  inductive type
  | ref: class_name α → type
  | data: Type → type

  instance : has_coe Type (type α) := ⟨type.data α⟩
end
open type

/- A program signature consists of: a map from class names to class declarations, and a class name of the root object. A class declaration (of some class self) consists of a map from field names to field declarations, a map from method names to method declarations, and a method name that indicates a constructor. A field declaration consists of a type. A method declaration consists of a map from parameter names to parameter declarations. A parameter declaration consists of a type. -/
section variables {α : Type} [names α]
    {self : class_name α}
    {m : method_name self}
  structure pdecl (p : param_name m) :=
    (type : type α)
  structure mdecl (m : method_name self) :=
    (pdecl (p : param_name m) : pdecl p)
  structure fdecl (f : field_name self) :=
    (type : type α)
  structure cdecl (self : class_name α) :=
    (fdecl (f : field_name self) : fdecl f)
    (mdecl (m : method_name self) : mdecl m)
    (ctor : method_name self)
-- Design choice: constructors and methods are treated uniformly.
end

class signature (α : Type) extends names α : Type 1 :=
(cdef (x : class_name α): cdecl x) (main: class_name α)

def param_type {α : Type} [signature α]
  {self : class_name α} {m : method_name self}
  (p : param_name m) : type α :=
(((signature.cdef self).mdecl m).pdecl p).type

def field_type {α : Type} [signature α]
  {self : class_name α} (f : field_name self) : type α :=
((signature.cdef self).fdecl f).type

def class_type {α : Type} [signature α]
  (self : class_name α) : type α :=
(ref self)

/- A variable context is a list of types; a local variable is encoded by an index in this context. Local variables do not have a name. -/
@[reducible]
def context (α : Type) [names α] : Type 1 := list (type α)

/- Given a signature, we consider type environments to consist of: a class name, a method name, and declared local variables. -/
structure tenv (α : Type) [signature α] : Type 1 :=
(self : class_name α)
(current : method_name self)
(locals : context α)

/- A note on terminology. Parameter: as declared in signature. Argument: a pure expression as supplied in a method call. -/

/- Within a typing environment, we refer to numerous things. This refers to an object identity of the enclosed class. A local variable refers to the index within the declared local variables. A parameter refers to a parameter name of the current method. A field refers to a field within the enclosed class. -/
structure tvar {α : Type} 

structure lvar {α : Type} [signature α] (e : tenv α)
  (ty : type α) : Type 1
:= (idx : list_at ty e.locals)

structure pvar {α : Type} [signature α] (e : tenv α)
  (ty : type α) : Type 1 :=
(idx : list_at ty (method_params e.current))

structure fvar {α : Type} [signature α] (e : tenv α)
  (ty : type α) : Type 1
:= (idx : field_name e.self) (H : ty = field_type idx)

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

/- A pure expression evaluates to a value of a particular type. Such expressions are either: a constant data value, a function application on data values, value lookup in environment, referential equality check. -/
inductive pexp {α : Type} [signature α] (e : tenv α) :
  type α → Type 1
| value (γ : Type) : γ → pexp γ
| apply (γ δ : Type) : pexp (γ → δ) → pexp γ → pexp δ
| lookup {ty : type α} : rvar e ty → pexp ty
| requal (c : class_name α) : pexp (ref c) → pexp (ref c) → pexp bool

/- Given a typing environment and a list of types, we have an argument list of variables with matching types. -/
inductive arglist {α : Type} [signature α] (e : tenv α) :
  list (type α) → Type 1
| nil : arglist []
| cons (x : type α) (xs : list (type α)) : pexp e x → arglist xs → arglist (x::xs)

/- A statement within a typing environment is either: a skip, a sequential composition, a branch, a loop, an assignment, an asynchronous method call, an object allocation. -/
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

/- A program with a given program signature associates to each method of each class a program block. A program block associated to a method consists of: local variable declarations, and a statement within a typing environment. -/
structure pblock {α : Type} [signature α]
  {self : class_name α} (m : method_name self) : Type 1 :=
(locals : context α) (S : stmt (tenv.mk self m locals))

structure program {α : Type} [signature α] : Type 1 :=
(body {self : class_name α} (m : method_name self): pblock m)
