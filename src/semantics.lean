-- (C) Copyright 2019, Hans-Dieter Hiep

import syntax

open signature type pexp

/-
We have the following class of dynamic types.
Given a finite set,
there can always be given a fresh instance not in that set.
(with thanks to Johannes Hölzl)
-/
class dynamic (β : Type) :=
(fresh: finset β → β)
(fresh_is_new: ∀x : finset β, (fresh x) ∉ x)
open dynamic

/-
Fix a signature (and global names).
We treat objects transparently.
Each object is associated to a single class name.
Equality is decidable for objects of the same class.
Given a set of objects, we can always construct some new object.
-/
class objects (α β : Type) extends signature α, dynamic β :=
(class_of: β → class_name α)
(equality (x y : β): class_of x = class_of y → bool)
open objects

/-
We treat values as being of a type.
A value of a reference type is an object of the same class.
A value of a data type is a term of the type in the host language.
-/
inductive value {α : Type} (β : Type) [objects α β] : type α → Type 1
| object (o : β) : value (ref (class_of α o))
| term {γ : Type} : γ → value (data α γ)

-- Projection of value to object
def value.objective {α β : Type} [objects α β] {c : class_name α}
(x : value β (ref c)) : β :=
begin cases x, apply x_1 end

lemma value.obj_class {α β : Type} [objects α β] {c : class_name α}
(x : value β (ref c)) : class_of α (value.objective x) = c :=
begin cases x, unfold value.objective end

-- Projection of value to term
def value.terminal {α : Type} (β : Type) [objects α β] {γ : Type}
(x : value β (data α γ)) : γ :=
begin cases x, apply x_a end

/-
Given two values of reference type,
we can decide referential equality.
-/
def value.ref_equal {α β : Type} [objects α β] {c : class_name α}
(x : value β (ref c)) (y : value β (ref c)) : bool :=
let H : class_of α (value.objective x) =
    class_of α (value.objective y) := begin
    repeat {rewrite value.obj_class}
end in equality (value.objective x) (value.objective y) H

open value

/-
For class C we have a state space Σ(C) consisting of:
an assignment of fields to values.
-/
structure state_space {α : Type} (β : Type) [objects α β]
(self : class_name α) : Type 1 :=
(map (f : field_name self) : value β (field_type f))

/-
Given a list of types,
we have a value list of values with matching types.
-/
inductive vallist {α : Type} (β : Type) [objects α β] : list (type α) → Type 1
| nil : vallist []
| cons {x : type α} {xs : list (type α)} :
    value β x → vallist xs → vallist (x::xs)

/-
Given a value list, and an index of its type list, we can obtain a value.
-/
def vallist.lookup {α β : Type} [objects α β] :
Π {l : context α} {ty : type α}, vallist β l → list_at ty l → value β ty
| (x :: xs) ._ (vallist.cons (v : value β x) _)
    (list_at.head .(x) .(xs)) := v
| (x :: xs) ty (vallist.cons _ (ys : vallist β xs))
    (list_at.tail .(x) (zs : list_at .(ty) xs)) := vallist.lookup ys zs

/-
Given a signature and method name m,
we have a argument space Σ(m) consisting
an assignment of method parameters to values.
-/
structure arg_space {α : Type} (β : Type) [objects α β]
{self : class_name α} (m : method_name self) : Type 1 :=
(map : vallist β (method_params m))

/-
Given a type environment,
we consider an assignment to consist of:
a state space (of the self class),
an argument space (of the current method),
a value list (of the local variables)
-/
structure assignment {α : Type} (β : Type) [objects α β] (e : tenv α) :=
(state : state_space β e.self)
(args : arg_space β e.current)
(store : vallist β e.locals)

def assignment.lookup {α β : Type} [objects α β] {e : tenv α}
(σ : assignment β e) (tx : type α) : rvar e tx → value β tx
| (rvar.fvar f) := eq.mpr (congr_arg _ f.H) (σ.state.map f.idx)
| (rvar.pvar p) := σ.args.map.lookup p.idx
| (rvar.lvar l) := σ.store.lookup l.idx

/-
NOTE: the definition for (rvar.fvar f) was found by the following proof,
for matching the type of tx to that of the field.

begin
    have H : (tx = field_type f.idx), apply f.H,
    rewrite H,
    exact σ.state.map f.idx
end
-/

/-
Evaluating a pure expression in an assignment.
-/
def eval {α β : Type} [objects α β] (e : tenv α) (σ : assignment β e)
: Π {ty : type α}, pexp e ty → value β ty
| bool (requal (c : class_name α)
  (l : pexp e (ref c)) (r : pexp e (ref c))) :=
    term β (ref_equal (eval l) (eval r))
| ty (lookup (r : rvar e ty)) := σ.lookup ty r
| _ (const .(e) (γ : Type) (v : γ)) := term β v
| _ (apply (γ : Type) δ
  (pl : pexp e (γ → δ))
  (pr : pexp e γ)) :=
    term β ((terminal β (eval pl)) (terminal β (eval pr)))
