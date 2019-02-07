-- (C) Copyright 2019, Hans-Dieter Hiep

import syntax

universes u
variables (α : Type) (β : Type)

open type
open pexp

/-
We treat objects transparently.
Each object is associated to a single class name.
Given a set of objects, we can always construct some new object.
-/
class objects [global_names α] :=
(class_of: β → class_name α)
(new: finset β → β)
(new_is_new: ∀x : finset β, (new x) ∉ x)

def objects.type_of {β : Type} [global_names α] [objects α β] (o : β) : type α :=
    ref (objects.class_of α o)

open objects

/-
We treat values as being of a type.
A value of a reference type is an object of the same class.
A value of a data type is a term of the type in the host language.
-/
inductive value {α : Type} [global_names α] [objects α β] : type α → Type 1
| obj (o : β) : value (type_of α o)
| term {γ : Type} : γ → value (data α γ)

open value

/-
Given a signature and class C,
we have a state space Σ(C) consisting of
an assignment of fields to values.
-/
structure state_space {α : Type} [global_names α] [objects α β] (sig : signature α)
(self : class_name α) : Type 1 :=
(map (f : field_name self) : value β (sig.field_type f))

/-
Given a list of types,
we have a value list of values with matching types.
-/
inductive vallist {α : Type} [global_names α] [objects α β] : list (type α) → Type 1
| nil : vallist []
| cons {x : type α} {xs : list (type α)} :
    value β x → vallist xs → vallist (x::xs)

/-
Given a value list, and an index of its type list, we can obtain a value.
-/
def vallist.lookup {α : Type} [global_names α] [objects α β] :
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
structure arg_space {α : Type} [global_names α] [objects α β] (sig : signature α)
{self : class_name α} (m : method_name self) : Type 1 :=
(map : vallist β (sig.method_params m))

/-
Given a type environment,
we consider an assignment to consist of:
a state space (of the self class),
an argument space (of the current method),
a value list (of the local variables)
-/
structure assignment {α : Type} [global_names α] [objects α β] (e : tenv α) :=
(state : state_space β e.sig e.self)
(args : arg_space β e.sig e.current)
(store : vallist β e.locals)

def assignment.lookup {α β : Type} [global_names α] [objects α β] {e : tenv α}
(σ : assignment β e) (tx : type α) : rvar e tx → value β tx
| (rvar.fvar f) := eq.mpr (congr_arg _ f.H) (σ.state.map f.idx)
| (rvar.pvar p) := σ.args.map.lookup β p.idx
| (rvar.lvar l) := σ.store.lookup β l.idx

/-
NOTE: the definition for (rvar.fvar f) was found by the following proof,
for matching the type of tx to that of the field.

begin
    have H : (tx = e.sig.field_type f.idx), apply f.H,
    rewrite H,
    exact σ.state.map f.idx
end
-/

/-
Evaluating a pure expression in an assignment.
-/
def eval {α : Type} [global_names α] [objects α β] (e : tenv α)
(σ : assignment β e) : Π {ty : type α}, pexp e ty → value β ty
| bool (requal (c : class_name α) (l : pexp e (ref c)) (r : pexp e (ref c))) := sorry
| ty (lookup (r : rvar e ty)) := sorry
| _ (const .(e) (γ : Type) (v : γ)) := term β v
| (γ : Type) (apply .(γ) δ pl pr) := sorry
