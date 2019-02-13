-- (C) Copyright 2019, Hans-Dieter Hiep

import data.fintype data.finmap data.bool data.vector data.list
import util

variable {α : Type}

/- Each program has names. Names consist of a finite set of class names. To each class name, there an associated finite set of field and method names. To each method name, there is an associated finite set of parameter names. -/
class names (α : Type) :=
  (decidable_name: decidable_eq α)
  (Nc: finset α)
  (Nf {x : α} (H: x ∈ Nc): finset α)
  (Nm {x : α} (H: x ∈ Nc): finset α)
  (Np {x : α} {H: x ∈ Nc} {y : α} (G : y ∈ Nm H): finset α)
instance names.decidable [names α]:
  decidable_eq α := names.decidable_name α

section -- (scope: [names α], self, m)
  variable [names α]
  /- We make use of subtypes, to demonstrate instances of fintype. Whenever we have established that these types are finite, we obtain decidable equality for functions that take these types as domain (thanks to Johannes Hölzl). This fact turns out to be crucial for semantics. -/
  @[reducible]
  def class_name (α : Type) [names α] :=
    {name : α // name ∈ names.Nc α}
  variable {self : class_name α}
  @[reducible]
  def field_name (self : class_name α) :=
    {name : α // name ∈ names.Nf self.property}
  @[reducible]
  def method_name (self : class_name α) :=
    {name : α // name ∈ names.Nm self.property}
  @[reducible]
  def param_name (m : method_name self) :=
    {name : α // name ∈ names.Np m.property}
  /- A type in our object language is either: a reference type (by class name), or a data type from the host language. A variable context is a list of types; a local variable is encoded by an index in this context. Local variables do not have a name. -/
  structure datatype :=
    (host : Type)
    (default: host)
    (decidable_data: decidable_eq host)
  instance datatype.to_sort : has_coe_to_sort datatype :=
    {S := Type, coe := λS, S.host}
  instance datatype.host_decidable (γ : datatype) :
    decidable_eq γ := γ.decidable_data
  instance datatype.host_inhabited (γ : datatype) :
    inhabited γ := ⟨γ.default⟩
  inductive type (α : Type) [names α]
  | ref: class_name α → type
  | data: datatype → type
  @[reducible] def boolean (α : Type) [names α] : type α :=
    type.data α ⟨bool, ff, bool.decidable_eq⟩
  /- A local variable context is a list of types. -/
  @[reducible] def context (α : Type) [names α] := list (type α)

  /- A class declaration (of some class self) consists of a map from field names to field declarations, a map from method names to method declarations, and a method name that indicates a constructor. A field declaration consists of a type. A method declaration consists of a map from parameter names to parameter declarations. A parameter declaration consists of a type. -/
  variable {m : method_name self}
  structure pdecl (p : param_name m) :=
    (type : type α)
  structure mdecl (m : method_name self) :=
    (pdecl (p : param_name m) : pdecl p)
  structure fdecl (f : field_name self) :=
    (type : type α)
  -- Design choice: constructors and methods are treated uniformly.
  structure cdecl (self : class_name α) :=
    (fdecl (f : field_name self) : fdecl f)
    (mdecl (m : method_name self) : mdecl m)
    (ctor : method_name self)
end
open type

/- A program signature consists of: a map from class names to class declarations, and a class name of the root object. -/
class signature (α : Type) extends names α : Type 1 :=
(cdef (x : class_name α): cdecl x) (main: class_name α)

variable [signature α]
variable {self : class_name α} 
variable {m : method_name self}

def param_type (p : param_name m) : type α :=
  (((signature.cdef self).mdecl m).pdecl p).type
def field_type (f : field_name self) : type α :=
  ((signature.cdef self).fdecl f).type
def constructor (self : class_name α) : method_name self :=
  (signature.cdef self).ctor
def class_type (self : class_name α) : type α :=
  (ref self)

/- Given a signature and an enclosing class, we consider type environments to consist of: a method name, and declared local variables. -/
structure tenv (self : class_name α) :=
  (current : method_name self)
  (locals : context α)
def tenv.self (e : tenv self) : class_name α := self
open tenv

/- A note on terminology. Parameter: as declared in signature. Argument: a pure expression as supplied in a method call. -/

/- Within a typing environment, we refer to numerous things. This refers to an object identity of the enclosed class. A local variable refers to the index within the declared local variables. A parameter refers to a parameter name of the current method. A field refers to a field within the enclosed class. -/
variables (e : tenv self) (ty : type α)
structure tvar :=
  (H : ty = ref e.self)
structure lvar :=
  (idx : list_at ty e.locals)
structure pvar :=
  (idx : param_name e.current) (H : ty = param_type idx)
structure fvar :=
  (idx : field_name e.self) (H : ty = field_type idx)
-- Store variable (LHS only)
inductive svar
| fvar: fvar e ty → svar
| lvar: lvar e ty → svar
-- Read variable (RHS only)
inductive rvar
| tvar: tvar e ty → rvar
| fvar: fvar e ty → rvar
| pvar: pvar e ty → rvar
| lvar: lvar e ty → rvar
/- A pure expression within a typing environment is either: a constant data value, a function application on data values, value lookup in environment, referential equality check. -/
inductive pexp : type α → Type 1
| const {γ : datatype}: γ → pexp (data α γ)
| apply {γ δ : datatype}: (γ.host → δ.host) → pexp (data α γ) →
    pexp (data α δ)
| lookup {ty : type α}: rvar e ty → pexp ty
| requal {c : class_name α}:
    pexp (ref c) → pexp (ref c) → pexp (boolean α)
/- An argument list assigns to each parameter of a method a variable within some typing environment of the right type. -/
structure arglist {c : class_name α} (m : method_name c) :=
  (map (p : param_name m) : pexp e (param_type p))
/- A statement within a typing environment is either: a skip, a sequential composition, a branch, a loop, an assignment, an asynchronous method call, an object allocation. -/
inductive stmt {α : Type} [signature α]
    {self : class_name α} : Π (e : tenv self), Type 1
| ite {e : tenv self}:
    pexp e (boolean α) → list (stmt e) → list (stmt e) → stmt e
| while {e : tenv self}:
    pexp e (boolean α) → list (stmt e) → stmt e
| assign {e : tenv self} {ty : type α}
    (l : svar e ty): pexp e ty → stmt e
| async {e : tenv self} {c : class_name α} {m : method_name c}
    {H : m ≠ constructor c}
    (o : rvar e (ref c))
    (τ : arglist e m): stmt e
| alloc {e : tenv self} {c : class_name α}
    (l : svar e (ref c))
    (τ : arglist e (constructor c)): stmt e
-- TODO: get nested definition working

/- A program with a given program signature associates to each method of each class a program block. A program block associated to a method consists of: local variable declarations, and a statement within a typing environment. -/
structure pblock {self : class_name α} (m : method_name self) :=
  (locals : context α)
  (S : stmt (tenv.mk m locals))
structure program (α : Type) [signature α] :=
  (body {self : class_name α} (m : method_name self): pblock m)
