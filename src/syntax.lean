-- (C) Copyright 2019, Hans-Dieter Hiep

import data.finmap data.bool data.vector data.list
import util

/- Each program has names. Names consist of a finite set of class names. To each class name, there an associated finite set of field and method names. To each method name, there is an associated finite set of parameter names. -/
class names (α : Type) :=
(Nc: finset α)
(Nf {x : α} (H: x ∈ Nc): finset α)
(Nm {x : α} (H: x ∈ Nc): finset α)
(Np {x : α} {H: x ∈ Nc} {y : α} (G : y ∈ Nm H): finset α)

section variables {α : Type} [names α]
  section open names
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
  /- A type in our object language is either: a reference type (by class name), or a data type from the host language. A variable context is a list of types; a local variable is encoded by an index in this context. Local variables do not have a name. -/
  inductive type (α : Type) [names α]
  | ref: class_name α → type
  | data: Type → type
  instance : has_coe Type (type α) := ⟨type.data α⟩
  /- A local variable context is a list of types. -/
  @[reducible] def context (α : Type) [names α] := list (type α)

  /- A program signature consists of: a map from class names to class declarations, and a class name of the root object. A class declaration (of some class self) consists of a map from field names to field declarations, a map from method names to method declarations, and a method name that indicates a constructor. A field declaration consists of a type. A method declaration consists of a map from parameter names to parameter declarations. A parameter declaration consists of a type. -/
  section variables {self : class_name α} {m : method_name self}
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
end

class signature (α : Type) extends names α : Type 1 :=
(cdef (x : class_name α): cdecl x) (main: class_name α)

variables {α : Type} [signature α]
open type

section variables {self : class_name α} {m : method_name self}
  def param_type (p : param_name m) : type α :=
    (((signature.cdef self).mdecl m).pdecl p).type
  def field_type (f : field_name self) : type α :=
    ((signature.cdef self).fdecl f).type
  def class_type (self : class_name α) : type α :=
    (ref self)
end

/- Given a signature, we consider type environments to consist of: a class name, a method name, and declared local variables. -/
structure tenv (α : Type) [signature α] : Type 1 :=
(self : class_name α)
(current : method_name self)
(locals : context α)

/- A note on terminology. Parameter: as declared in signature. Argument: a pure expression as supplied in a method call. -/

/- Within a typing environment, we refer to numerous things. This refers to an object identity of the enclosed class. A local variable refers to the index within the declared local variables. A parameter refers to a parameter name of the current method. A field refers to a field within the enclosed class. -/
section variable (e : tenv α)
  section variable (ty : type α)
    structure tvar := (H : ty = ref e.self)
    structure lvar := (idx : list_at ty e.locals)
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
  end
  /- A pure expression within a typing environment is either: a constant data value, a function application on data values, value lookup in environment, referential equality check. -/
  inductive pexp : type α → Type 1
  | const {γ : Type}: γ → pexp γ
  | apply {γ δ : Type}: pexp (γ → δ) → pexp γ → pexp δ
  | lookup {ty : type α}: rvar e ty → pexp ty
  | requal {c : class_name α}:
      pexp (ref c) → pexp (ref c) → pexp bool
  /- An argument list assigns to each parameter of a method a variable within some typing environment of the right type. -/
  structure arglist {c : class_name α} (m : method_name c) :=
    (map (p : param_name m) : pexp e (param_type p))
  /- A statement within a typing environment is either: a skip, a sequential composition, a branch, a loop, an assignment, an asynchronous method call, an object allocation. -/
  inductive stmt : Type 1
  | skip: stmt
  | seq: stmt → stmt → stmt
  | ite: pexp e bool → stmt → stmt → stmt
  | while: pexp e bool → stmt → stmt
  | assign {ty : type α}
      (l : svar e ty): pexp e ty → stmt
  | async {c : class_name α} {m : method_name c}
      (o : rvar e (ref c))
      (τ : arglist e m): stmt
  | alloc {c : class_name α}
      (l : svar e (ref c)): stmt
end

/- A program with a given program signature associates to each method of each class a program block. A program block associated to a method consists of: local variable declarations, and a statement within a typing environment. -/
structure pblock {self : class_name α} (m : method_name self) :=
  (locals : context α)
  (S : stmt (tenv.mk self m locals))
structure program :=
  (body {self : class_name α} (m : method_name self): pblock m)
