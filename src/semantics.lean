-- (C) Copyright 2019, Hans-Dieter Hiep

import syntax data.stream

open stream signature type pexp nat

/- Fix a signature (and global names). We treat objects transparently. Each object is associated to a single class name. Given a finite set of object identities, there can always be a fresh identity not in that set (thanks to Johannes Hölzl). Allocation of a fresh identity results in the same class name. Equality is decidable for objects. -/
class objects (α β : Type) extends signature α :=
(alloc: finset β → class_name α → β)
(class_of: β → class_name α)
(decidable_object: decidable_eq β)

(alloc_is_new (x : finset β) (c : class_name α):
  (alloc x c) ∉ x)
(alloc_class_of (x : finset β) (c : class_name α):
  class_of (alloc x c) = c)
open objects

/- We treat values as being of a type. A value of a reference type is an object of the same class, or null. A value of a data type is a term of the type in the host language. -/
section variables {α : Type} (β : Type) [objects α β]
  inductive value : type α → Type 1
  | object (o : β) : value (ref (class_of α o))
  | null (c : class_name α) : value (ref c)
  | term {γ : Type} : γ → value (data α γ)
end
section variables {α β : Type} [objects α β] {c : class_name α}
  -- Projection of value to term
  def value.terminal {γ : Type} (x : value β (data α γ)) : γ :=
    begin cases x, apply x_a end
  section variable {x : value β (ref c)}
    -- Projection of value to object (if not null)
    def value.objective (H: x ≠ value.null c): β :=
      begin cases x, apply x_1, exfalso, apply H, refl end
    -- The class of object values corresponds to their reference type
    lemma value.obj_class (H: x ≠ value.null c):
        class_of α (value.objective H) = c :=
      begin cases x, unfold value.objective,
        exfalso, apply H, refl end
    -- Checking equality with null is decidable
    instance decidable_value_null:
        decidable (x = value.null c) :=
      begin cases x, apply is_false, intro, cases a,
        apply is_true, refl end
  end
  -- Checking equality of objective values is decidable
  instance decidable_value_objective
      {x : value β (ref c)} {y : value β (ref c)}
      {P : x ≠ value.null c} {Q : y ≠ value.null c} :
      decidable (value.objective P = value.objective Q) :=
    begin apply (decidable_object α β) end
  /- Given two values of reference type, we can decide referential equality. -/
  def value.ref_equal
      (x : value β (ref c))
      (y : value β (ref c)) : bool :=
    if P : x = value.null c then to_bool (y = value.null c)
    else if Q : y = value.null c then false
      else to_bool (value.objective P = value.objective Q)
end
open value

/- For class C we have a state space Σ(C) consisting of: an assignment of fields to values. -/
structure state_space {α : Type} (β : Type) [objects α β]
  (self : class_name α) : Type 1 :=
(map (f : field_name self) : value β (field_type f))

/- Given a list of types, we have a value list of values with matching types. -/
inductive vallist {α : Type} (β : Type) [objects α β] :
  list (type α) → Type 1
| nil : vallist []
| cons {x : type α} {xs : list (type α)} :
  value β x → vallist xs → vallist (x::xs)

/- Given a value list, and an index of its type list, we can obtain a value. -/
def vallist.lookup {α β : Type} [objects α β] :
  Π {l : context α} {ty : type α}, vallist β l → list_at ty l →
  value β ty
| (x :: xs) ._ (vallist.cons (v : value β x) _)
  (list_at.head .(x) .(xs)) := v
| (x :: xs) ty (vallist.cons _ (ys : vallist β xs))
  (list_at.tail .(x) (zs : list_at .(ty) xs)) :=
    vallist.lookup ys zs

/- Given a signature and method name m, we have a argument space Σ(m) consisting an assignment of method parameters to values. -/
structure arg_space {α : Type} (β : Type) [objects α β]
  {self : class_name α} (m : method_name self) : Type 1 :=
(map : vallist β (method_params m))

/- Given a type environment, we consider an assignment to consist of: a state space (of the self class), an argument space (of the current method), a value list (of the local variables) -/
structure assignment {α : Type} (β : Type) [objects α β]
  (e : tenv α) :=
(state : state_space β e.self)
(args : arg_space β e.current)
(store : vallist β e.locals)

def assignment.lookup {α β : Type} [objects α β] {e : tenv α}
  (σ : assignment β e) (tx : type α) : rvar e tx → value β tx
| (rvar.fvar f) := eq.mpr (congr_arg _ f.H) (σ.state.map f.idx)
| (rvar.pvar p) := σ.args.map.lookup p.idx
| (rvar.lvar l) := σ.store.lookup l.idx

/- NOTE: the definition for (rvar.fvar f) was found by the following proof,
for matching the type of tx to that of the field.

begin
    have H : (tx = field_type f.idx), apply f.H,
    rewrite H,
    exact σ.state.map f.idx
end -/

/- Evaluating a pure expression in an assignment. -/
def peval {α β : Type} [objects α β] {e : tenv α}
  (σ : assignment β e) : Π {ty : type α}, pexp e ty → value β ty
| bool (requal (c : class_name α)
    (l : pexp e (ref c)) (r : pexp e (ref c))) :=
  term β (ref_equal (peval l) (peval r))
| ty (lookup (r : rvar e ty)) := σ.lookup ty r
| _ (value _ (γ : Type) (v : γ)) := term β v
| _ (apply (γ : Type) δ (pl : pexp e (γ → δ)) (pr : pexp e γ)) :=
  term β ((terminal β (peval pl)) (terminal β (peval pr)))

/- Evaluating a statement in an assignment generates a stream of assignments. -/
def eval {α β : Type} [objects α β] {e : tenv α}
  (σ : assignment β e) : stmt e →
  stream (option (assignment β e))
| (stmt.skip e) := cons σ (const none)
| _ := sorry
