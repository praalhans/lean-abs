/- Copyright 2019 (c) Hans-Dieter Hiep. All rights reserved. Released under MIT license as described in the file LICENSE. -/

import data.fintype data.finmap data.bool data.vector data.list
import util

variable {α : Type}

/- Each program has names. Names consist of a finite set of class names, a finite set of record names, and a finite set of symbol names. To each class name, there an associated finite set of field and method names. To each method name, there is an associated finite set of parameter names. There is a built-in record name, boolean. -/
class names (α : Type) :=
  (decidable_name: decidable_eq α)
  (Nc: finset α)
  (Nr: finset α)
  (Ns: finset α)
  (Nf {x : α} (H: x ∈ Nc): finset α)
  (Nm {x : α} (H: x ∈ Nc): finset α)
  (Np {x : α} {H: x ∈ Nc} {y : α} (G : y ∈ Nm H): finset α)
  (Nboolean : α)
  (Hboolean : Nboolean ∈ Nr)
instance names.decidable [names α]:
  decidable_eq α := names.decidable_name α

/- We make use of subtypes, to demonstrate instances of fintype. Whenever we have established that these types are finite, we obtain decidable equality for functions that take these types as domain (thanks to Johannes Hölzl). This fact turns out to be crucial for semantics. -/
@[reducible]
def class_name (α : Type) [names α] :=
  {name : α // name ∈ names.Nc α}
@[reducible]
def record_name (α : Type) [names α] :=
  {name : α // name ∈ names.Nr α}
@[reducible]
def symbol_name (α : Type) [names α] :=
  {name : α // name ∈ names.Ns α}
@[reducible]
def boolean_name (α : Type) [names α] : record_name α :=
  ⟨names.Nboolean α, names.Hboolean α⟩
@[reducible]
def field_name [names α] (self : class_name α) :=
  {name : α // name ∈ names.Nf self.property}
@[reducible]
def method_name [names α] (self : class_name α) :=
  {name : α // name ∈ names.Nm self.property}
@[reducible]
def param_name [names α]
    {self : class_name α} (m : method_name self) :=
  {name : α // name ∈ names.Np m.property}

/- A type in our object language is either: a reference type (by class name), or a data type (by record name). -/
@[derive decidable_eq]
inductive type (α : Type) [names α]
| ref: class_name α → type
| data: record_name α → type

/- A variable context is a list of types; a local variable is encoded by an index in this context. Local variables do not have a name. -/
@[reducible] def context (α : Type) [names α] := list (type α)
/- Boolean is a built-in data type. -/
@[reducible] def boolean (α : Type) [names α] : type α :=
  (type.data (boolean_name α))

/- A class declaration (of some class self) consists of a map from field names to field declarations, a map from method names to method declarations, and a method name that indicates a constructor. A field declaration consists of a type. A method declaration consists of a map from parameter names to parameter declarations. A parameter declaration consists of a type. -/
structure pdecl [names α]
    {self : class_name α} {m : method_name self}
    (p : param_name m) :=
  (type : type α)
structure mdecl [names α]
    {self : class_name α} (m : method_name self) :=
  (pdecl (p : param_name m) : pdecl p)
structure fdecl [names α]
    {self : class_name α} (f : field_name self) :=
  (type : type α)
-- Design choice: constructors and methods are treated uniformly.
structure cdecl [names α] (self : class_name α) :=
  (fdecl (f : field_name self) : fdecl f)
  (mdecl (m : method_name self) : mdecl m)
  (ctor : method_name self)
  
/- A symbol declaration consists of a list of types of arguments, together with a resultant type. The arity of a symbol declaration is the length of the list of argument types. -/
structure sdecl (α : Type) [names α] :=
  (args : list (type α))
  (result : type α)
def sdecl.arity {α : Type} [names α] (s : sdecl α) :=
  list.length s.args

/- A signature consists of: a map from class names to class declarations, a map from symbols names to symbol declarations, and a class name of the root object. -/
class signature (α : Type) extends names α : Type 1 :=
  (cdef (x : class_name α): cdecl x)
  (sdef (x : symbol_name α) : sdecl α)
  (main: class_name α)

variable [signature α]
variable {self : class_name α}

/- Each parameter is associated to a type, each field is associated to a type, and each class name is associated to a constructor method name. -/
def param_type {m : method_name self} (p : param_name m)
  : type α := (((signature.cdef self).mdecl m).pdecl p).type
def field_type (f : field_name self) : type α :=
  ((signature.cdef self).fdecl f).type
def ctor (self : class_name α) : method_name self :=
  (signature.cdef self).ctor
/- A symbol with zero arity is a constant symbol, a symbol with non-zero arity is a function symbol. Each symbol is associated to a result type. A function symbol is associated to a list of argument types. -/
@[derive decidable_eq]
structure symbol (args : list (type α)) (result : type α)
    (s : symbol_name α) :=
  (H: args = (signature.sdef s).args)
  (G: result = (signature.sdef s).result)

/- Given a signature and an enclosing class, we consider type environments to consist of: a method name, and declared local variables. -/
@[derive decidable_eq]
structure tenv (self : class_name α) :=
  (current : method_name self)
  (locals : context α)
def tenv.self (e : tenv self) : class_name α := self

/- A note on terminology. Parameter: as declared in signature. Argument: a pure expression as supplied in a method call, or as supplied to a function symbol. -/

/- Within a typing environment, we refer to numerous things. This refers to an object identity of the enclosed class. A local variable refers to the index within the declared local variables. A parameter refers to a parameter name of the current method. A field refers to a field within the enclosed class. -/
section
variables (e : tenv self) (ty : type α)
@[derive decidable_eq]
structure tvar :=
  (H : ty = type.ref e.self)
@[derive decidable_eq]
structure lvar :=
  (idx : list_at ty e.locals)
@[derive decidable_eq]
structure pvar :=
  (idx : param_name e.current) (H : param_type idx = ty)
@[derive decidable_eq]
structure fvar :=
  (idx : field_name e.self) (H : field_type idx = ty)
-- Store variable (LHS only)
@[derive decidable_eq]
inductive svar
| fvar: fvar e ty → svar
| lvar: lvar e ty → svar
-- Read variable (RHS only)
@[derive decidable_eq]
inductive rvar
| tvar: tvar e ty → rvar
| fvar: fvar e ty → rvar
| pvar: pvar e ty → rvar
| lvar: lvar e ty → rvar
end

/- A pure expression within a typing environment is either: a constant, a function application, value lookup in environment, referential equality check. -/
@[derive decidable_eq]
inductive pexp (e : tenv self) : list (type α) → Type 1
| const {ty : type α} {c : symbol_name α}:
    symbol [] ty c → pexp [ty]
| app {l : list (type α)} {ty : type α} (f : symbol_name α):
    symbol l ty f → pexp l → pexp [ty]
| lookup {ty : type α}:
    rvar e ty → pexp [ty]
| requal {c : class_name α}:
    pexp [type.ref c] → pexp [type.ref c] → pexp [boolean α]
| cons {ty : type α} {l : list (type α)}:
    pexp [ty] → pexp l → pexp (ty::l)
/- The encoding of a mutual inductive type fails in Lean 3.4.2. We currently encode this directly, by considering single expressions as expressions with a length one type list. Tuples of expressions are created by constructing lists of expressions of length one lists of types. There are no expressions of empty lists of types. -/
lemma pexp_not_nil {e : tenv self} {l : list (type α)}
  (p : pexp e l) : l ≠ [] :=
begin
  cases l, {intro, cases p}, {intro, cases a}
end

/- A method argument list assigns to each parameter of a method a pure expression within some typing environment of the right type. -/
@[derive decidable_eq]
structure marglist (e : tenv self)
    {c : class_name α} (m : method_name c) :=
  (map (p : param_name m) : pexp e [param_type p])

/- A statement within a typing environment is either: a skip, a sequential composition, a branch, a loop, an assignment, an asynchronous method call, an object allocation. -/
@[derive decidable_eq]
inductive stmt (e : tenv self) : bool → Type 1
| ite: pexp e [boolean α] → stmt tt → stmt tt → stmt ff
| while: pexp e [boolean α] → stmt tt → stmt ff
| assign {ty : type α} (l : svar e ty):
    pexp e [ty] → stmt ff
| async (c : class_name α) (m : method_name c)
    (H : m ≠ ctor c)
    (o : rvar e (type.ref c))
    (τ : marglist e m): stmt ff
| alloc (c : class_name α)
    (l : svar e (type.ref c))
    (τ : marglist e (ctor c)): stmt ff
| nil: stmt tt
| cons: stmt ff → stmt tt → stmt tt
/- The encoding of a nested inductive type failed at the moment in Lean 3.4.2. Instead, we encode the nesting ourselves: the boolean argument determines which constructors are applicable. It is true if it is a list of statements, false if it is a single statement (thanks to Mario Carneiro).  -/
@[reducible]
def statement (e : tenv self) := stmt e ff
variable {e : tenv self}
def stmt.from_list : list (statement e) → stmt e tt
| [] := stmt.nil e
| (x :: xs) := stmt.cons x (stmt.from_list xs)
def stmt.to_list : stmt e tt → list (statement e)
| (stmt.nil .(e)) := []
| (stmt.cons x xs) := (x :: stmt.to_list xs)

/- A program with a given program signature associates to each method of each class a program block. A program block associated to a method consists of: local variable declarations, and a statement within a typing environment. -/
structure pblock (m : method_name self) :=
  (locals : context α)
  (S : list (statement ⟨m,locals⟩))
def pblock.tenv {m : method_name self} (pb : pblock m) :=
  (tenv.mk m pb.locals)
structure program (α : Type) [signature α] :=
  (body {self : class_name α} (m : method_name self): pblock m)
