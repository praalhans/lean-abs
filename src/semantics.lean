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
  def value.unterm {γ : Type} (x : value β (data α γ)) : γ :=
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
  def value.requal: value β (ref c) → value β (ref c) → bool :=
    λx, λy, if P : x=value.null c then to_bool (y=value.null c)
      else if Q : y=value.null c then false
        else to_bool (value.objective P = value.objective Q)
end
open value

section variables {α : Type} (β : Type) [objects α β]
    (self : class_name α)
  /- For class C we have a state space Σ(C) consisting of an assignment of fields to values. -/
  structure state_space :=
    (map (f : field_name self) : value β (field_type f))
  /- For method m, we have a argument space Σ(m) consisting of an assignment of method parameters to values. -/
  structure arg_space [objects α β] {self : class_name α}
      (m : method_name self) :=
    (map (p : param_name m) : value β (param_type p))
  /- Given a list of types, we have a value list of values with matching types. -/
  inductive vallist : list (type α) → Type 1
  | nil : vallist []
  | cons {x : type α} {xs : list (type α)} :
    value β x → vallist xs → vallist (x::xs)
  /- An object space consists of: a this identity, a state space (of the self class). -/
  structure object_space :=
    (this : value β (ref self))
    (state : state_space β self)
end
section variables {α : Type} {β : Type} [objects α β]
    {self : class_name α} {o : object_space β self}
    {e : tenv self}
  /- An active process consists of: an argument space (of the current method), a value list (of the local variables), and a statement. -/
  structure active_process (o : object_space β self) (e : tenv self) :=
    (args : arg_space β e.current)
    (store : vallist β e.locals)
    (stmt : stmt e)
  /- Given a value list and an index in the list of types, we obtain a value. -/
  def vallist.lookup : Π {l : context α} {ty : type α},
      vallist β l → list_at ty l → value β ty
  | (x :: xs) ._ (vallist.cons (v : value β x) _)
    (list_at.head .(x) .(xs)) := v
  | (x :: xs) ty (vallist.cons _ (ys : vallist β xs))
    (list_at.tail .(x) (zs : list_at .(ty) xs)) :=
      vallist.lookup ys zs
  -- Given an active process, we can lookup the value of a read variable.
  def active_process.lookup  (P : active_process o e)
      {tx : type α} : rvar e tx → value β tx
  | (rvar.tvar t) := eq.mpr (congr_arg _ t.H) o.this
  | (rvar.fvar f) := eq.mpr (congr_arg _ f.H) $ o.state.map f.idx
  | (rvar.pvar p) := eq.mpr (congr_arg _ p.H) $ P.args.map p.idx
  | (rvar.lvar l) := P.store.lookup l.idx
  /- Evaluating a pure expression in an active process. -/
  def eval (P : active_process o e) : Π {ty : type α},
      pexp e ty → value β ty
  | bool (requal l r) := term β (requal (eval l) (eval r))
  | ty (lookup r) := P.lookup r
  | _ (const _ v) := term β v
  | _ (apply l r) := term β $ (unterm $ eval l) (unterm $ eval r)
  /- A process is either nil or an active process. -/
  inductive process (o : object_space β self)
  | nil : process
  | active {e : tenv self} (a : active_process o e) : process
  /- A local configuration is an object configuration and a process. -/
  structure local_config :=
    (o : object_space β self) (m : process o)
  /- A local step is a map from local configuration to local configuration. -/
end
