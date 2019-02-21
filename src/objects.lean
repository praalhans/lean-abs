/- Copyright 2019 (c) Hans-Dieter Hiep. All rights reserved. Released under MIT license as described in the file LICENSE. -/

import syntax

universe u

open signature list

/- Fix a signature. We consider an interpretation of reference types and data types. Reference types are interpreted as object identities. Each object identity is associated to a single class name. Equality is decidable for objects. Each record name is uniquely associated to a data type. A data type comprises an inhabited Lean type with decidable equality. The built-in boolean is associated to Lean's bool with false as default. -/
structure datatype :=
  (host : Type)
  (inhabited_host: inhabited host)
  (decidable_host: decidable_eq host)
instance datatype.decidable_eq (d : datatype) :
  decidable_eq d.host := d.decidable_host
instance datatype.inhabited_eq (d : datatype) :
  inhabited d.host := d.inhabited_host
def datatype.default (d : datatype) : d.host :=
  default d.host

class objects (α β : Type) extends signature α :=
(class_of: β → class_name α)
(decidable_object: decidable_eq β)
(data_type: record_name α → datatype)
(data_type_boolean:
  (data_type (boolean_name α)).host = bool)
(data_type_boolean_inhabited:
  (cast data_type_boolean (data_type (boolean_name α))
    .inhabited_host.default) = ff)
open objects

lemma data_type_booleanr {α β : Type} [objects α β] :
  bool = (data_type (boolean_name α)).host :=
begin symmetry, apply data_type_boolean end
instance objects.decidable_eq {α β : Type} [objects α β] :
  decidable_eq β := decidable_object α β

/- We treat values as being of a type. A value of a reference type is an object of the same class, or null. A value of a data type is a term of the associated type in Lean. -/
@[derive decidable_eq]
inductive value {α β : Type} [objects α β] : type α → Type
| object {c : class_name α} :
    {o : β // c = class_of α o} → value (type.ref c)
| null (c : class_name α) :
    value (type.ref c)
| term {r : record_name α} :
    (data_type r).host → value (type.data r)
/- The default value of a reference type is null, and the default value of a data type is the default in Lean. -/
instance value.inhabited {α β : Type} [objects α β] :
    Π{ty : type α}, inhabited (value ty)
| (type.ref c) := ⟨value.null c⟩
| (type.data r) := ⟨value.term (data_type r).default⟩
-- Projection of value to term
def value.unterm {α β : Type} [objects α β]
    {r : record_name α} : Π (x : value (type.data r)),
    (data_type r).host
| (value.term t) := t
-- Projection of boolean value to bool
def value.unbool {α β : Type} [objects α β] :
    Π (x : value (boolean α)), bool
| (value.term t) := cast (data_type_boolean α β) t
-- Projection of value to potential object
def value.unobject {α β : Type} [objects α β]
    {c : class_name α} : Π (x : value (type.ref c)), option β
| (value.object o) := o
| (value.null _) := none
def value.not_null {α β : Type} [objects α β]
    {c : class_name α} (x : value (type.ref c)) : Prop :=
  x ≠ value.null c
-- Projection of not-null value to object identity
def value.the_object {α β : Type} [objects α β]
    {c : class_name α} : Π (x : value (type.ref c)),
    value.not_null x → β
| (value.object o) _ := o
| (value.null .(c)) G := begin exfalso, apply G, refl end
lemma value.class_of_the_object {α β : Type} [objects α β]
  {c : class_name α} {x : value (type.ref c)}
  (G : value.not_null x) :
  class_of α (value.the_object x G) = c :=
begin
  cases x,
  {unfold value.the_object, apply eq.symm,
   simp [coe,lift_t,has_lift_t.lift],
   simp [coe_t,has_coe_t.coe,coe_b,has_coe.coe],
   exact x_a.property},
  {exfalso, apply G, refl}
end
-- Projection of value to object
def value.elim_object {α β : Type} [objects α β] {γ : Sort u}
    {c : class_name α} (v : value (type.ref c))
    (f : Π(o : {o : β // c = class_of α o}),
      v = value.object o → γ) (g : v = value.null c → γ) : γ :=
  match v, rfl : (∀ b, v = b → γ) with
  | (value.object o), h := f o h
  | (value.null .(c)), h := g h
  end

/- Given a list of types, we have a value list of values with matching types. -/
@[derive decidable_eq]
inductive vallist {α β : Type} [objects α β] :
    list (type α) → Type
| nil : vallist []
| cons {ty : type α} {l : list (type α)} :
  value ty → vallist l → vallist (ty::l)
def vallist.default {α β : Type} [objects α β] :
    Π(l : list (type α)), vallist l
| [] := vallist.nil
| (t :: l) := vallist.cons (default (value t))
    (vallist.default l)
instance vallist.inhabited {α β : Type} [objects α β]
    (l : list (type α)) : inhabited (vallist l) :=
  ⟨vallist.default l⟩
/- A value list of a single type is just a value. -/
def vallist.single {α β : Type} [objects α β] {ty : type α}
    (v : value ty) : vallist [ty] :=
  vallist.cons v vallist.nil
/- There is a unique value of a single value list. -/
def vallist.the {α β : Type} [objects α β] {ty : type α} :
    vallist [ty] → value ty
| (vallist.cons h vallist.nil) := h
/- A value list of a single type can be appended at the front to form a new value list. -/
def vallist.consl {α β : Type} [objects α β]
    {ty : type α} {l : list (type α)}
    (h : vallist [ty]) (t : vallist l) : vallist (ty :: l) :=
  vallist.cons (h.the) t
/- Given a value list and an index in the list of types, we obtain a value. -/
def vallist.lookup {α β : Type} [objects α β] {ty : type α} :
    Π {l : context α}, vallist l → list_at ty l → value ty
| (x :: xs) (vallist.cons v _) (list_at.here .(x) .(xs)) := v
| (x :: xs) (vallist.cons _ ys) (list_at.tail .(x) zs) :=
    vallist.lookup ys zs
/- Given a value list and an index and a new value, we obtain a new value list which updates the given index. -/
def vallist.update {α β : Type} [objects α β] {ty : type α} :
    Π {l : context α}, vallist l → list_at ty l →
    value ty → vallist l
| (x :: xs) (vallist.cons _ tl) (list_at.here .(x) .(xs)) v :=
    vallist.cons v tl
| (x :: xs) (vallist.cons v ys) (list_at.tail .(x) zs) w :=
    vallist.cons v (vallist.update ys zs w)

/- An interpretation consists of a mapping from constant symbols to values, and from function symbols to functions over value lists to values. -/
class interpret (α β : Type) extends objects α β :=
  (interp {args : list (type α)} {result : type α}
    {s : symbol_name α} (sym : symbol args result s):
    vallist args → value result)
