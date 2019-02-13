-- (C) Copyright 2019, Hans-Dieter Hiep

import syntax data.finsupp

open signature type pexp nat list

/- Fix a signature (and global names). We treat object identities transparently. Each object identity is associated to a single class name. Given a finite set of object identities, there can always be a fresh object identity not in that set (thanks to Johannes Hölzl). Allocation of a fresh object results in an object with the same class name as allocated. Equality is decidable for objects. -/
class objects (α β : Type) extends signature α :=
(alloc: finset β → class_name α → β)
(class_of: β → class_name α)
(decidable_object: decidable_eq β)
(alloc_is_new (x : finset β) (c : class_name α):
  (alloc x c) ∉ x)
(alloc_class_of (x : finset β) (c : class_name α):
  class_of (alloc x c) = c)
open objects

variables {α β : Type} [objects α β]
variable {c : class_name α}

instance objects.decidable : decidable_eq β :=
  decidable_object α β

/- We treat values as being of a type. A value of a reference type is an object of the same class, or null. A value of a data type is a term of the type in the host language. -/
@[derive decidable_eq]
inductive value (β : Type) [objects α β] : type α → Type 1
| object {c : class_name α} (o : β)
    (H : c = class_of α o) : value (ref c)
| null (c : class_name α) : value (ref c)
| term {γ : datatype} : γ → value (data α γ)
instance value.inhabited : Π{ty : type α}, inhabited (value β ty)
| (ref c) := ⟨value.null c⟩
| (data .(α) γ) := ⟨value.term β γ.default⟩
-- Projection of value to term
def value.unterm {γ : datatype} :
    Π (x : value β (data α γ)), γ.host
| (value.term .(β) t) := t
-- Projection of value to object
def value.unobject {c : class_name α} :
    Π (x : value β (ref c)), option β
| (value.object o _) := o
| (value.null _) := none

/- For class C we have a state space Σ(C) consisting of an assignment of fields to values. For method m, we have a argument space Σ(m) consisting of an assignment of method parameters to values. Given a list of types, we have a value list of values with matching types. An object space consists of: a this identity, a state space (of the self class). -/
@[derive decidable_eq]
structure arg_space (β : Type) [objects α β]
    {self : class_name α} (m : method_name self) :=
  (map (p : param_name m) : value β (param_type p))
structure state_space (β : Type) [objects α β]
    (self : class_name α) :=
  (map (f : field_name self) : value β (field_type f))
inductive vallist (β : Type) [objects α β] :
    list (type α) → Type 1
| nil : vallist []
| cons {ty : type α} {l : list (type α)} :
  value β ty → vallist l → vallist (ty::l)
def vallist.default (β : Type) [objects α β] :
    Π(l : list (type α)), vallist β l
| [] := vallist.nil β
| (t :: l) := vallist.cons (default (value β t))
    (vallist.default l)
instance vallist.inhabited (l : list (type α)) :
  inhabited (vallist β l) := ⟨vallist.default β l⟩
structure object_space (β : Type) [objects α β]
    (self : class_name α) :=
  (val : value β (ref self))
  (state : state_space β self)

variables {self : class_name α}

/- An active process consists of: an argument space (of the current method), a value list (of the local variables), and a statement. -/
structure active_process (this : object_space β self)
    (e : tenv self) :=
  (args : arg_space β e.current) (store : vallist β e.locals)
  (stmt : stmt e)
/- Given a value list and an index in the list of types, we obtain a value. -/
def vallist.lookup : Π {l : context α} {ty : type α},
    vallist β l → list_at ty l → value β ty
| (x :: xs) ._ (vallist.cons (v : value β x) _)
  (list_at.here .(x) .(xs)) := v
| (x :: xs) ty (vallist.cons _ (ys : vallist β xs))
  (list_at.tail .(x) (zs : list_at .(ty) xs)) :=
    vallist.lookup ys zs
-- Given an active process, we can lookup the value of a read variable.
variables {this : object_space β self} {e : tenv self}
def active_process.lookup (P : active_process this e)
    {tx : type α} : rvar e tx → value β tx
| (rvar.tvar t) := eq.mpr (congr_arg _ t.H) this.val
| (rvar.fvar f) := eq.mpr (congr_arg _ f.H) $ this.state.map f.idx
| (rvar.pvar p) := eq.mpr (congr_arg _ p.H) $ P.args.map p.idx
| (rvar.lvar l) := P.store.lookup l.idx
/- Evaluating a pure expression in an active process. -/
def eval (P : active_process this e) : Π {ty : type α},
    pexp e ty → value β ty
| bool (requal l r) := value.term β $ to_bool (eval l = eval r)
| _ (lookup r) := P.lookup r
| _ (const _ v) := value.term β v
| _ (apply f r) := value.term β $ f (eval r).unterm
/- A process is either nil or an active process. -/
inductive process (this : object_space β self)
| nil : process
| active {e : tenv self} (a : active_process this e) : process
/- An event is either an asynchronous method call of some caller object to a callee object, its method, and for each parameter an argument value. Or, an event is a method selection. -/
@[derive decidable_eq]
structure callsite (α β : Type) [objects α β] :=
  (o : β)
  (m : method_name (class_of α o))
  (τ : arg_space β m)
@[derive decidable_eq]
inductive event (α β : Type) [objects α β]
| call: β → callsite α β → event
| selection: callsite α β → event
def event.to_callsite : event α β → callsite α β
| (event.call _ c) := c
| (event.selection c) := c
instance event.event_to_callsite : has_coe (event α β)
  (callsite α β) := ⟨event.to_callsite⟩
/- A global history is a sequence of events. -/
@[reducible]
def global_history (α β : Type) [objects α β] := list (event α β)
/- There are two subsequences of a global history. The first consists only of call events with the object as callee (abstracted to its corresponding call site), the second consists only of selection events with the object as callee. -/
def event.is_call_to (α : Type) [objects α β] (x : β) :
    event α β → option (callsite α β)
| (event.call _ c) := if x = c.o then some c else none
| _ := none
def event.is_selection_of (α : Type) [objects α β] (x : β) :
    event α β → option (callsite α β)
| (event.selection c) := if x = c.o then some c else none
| _ := none
def global_history.calls_to (θ : global_history α β)
    (x : β) : list (callsite α β) :=
  θ.filter_map (event.is_call_to α x)
def global_history.selections_of (θ : global_history α β)
    (x : β) : list (callsite α β) :=
  θ.filter_map (event.is_selection_of α x)
reserve notation `!`:68
reserve notation `?`:68
infix ! := global_history.calls_to
infix ? := global_history.selections_of
/- A local history is obtained from a global history and an object identity: it consists of the outgoing calls, an method selections involving the object. -/
@[reducible]
def event.is_local_to (α : Type) [objects α β] (x : β) :
    event α β → Prop
| (event.call y _) := x = y -- same caller
| (event.selection c) := x = c.o -- same callee
instance event.decidable_local (o : β) (e: event α β) :
    decidable (event.is_local_to α o e) :=
  begin cases e; apply_instance end
def local_history (θ : global_history α β) (o : β) :=
  θ.filter (event.is_local_to α o)
/- The list of pending calls to an object is the list of calls to, with the selections removed. -/
def global_history.pending_calls_to (θ : global_history α β)
  (o : β) : list (callsite α β) := (θ!o).remove_all (θ?o)
/- We have an optional first pending call to an object. -/
def global_history.sched (θ : global_history α β)
    (o : β) : option (callsite α β) :=
  head (lift (θ.pending_calls_to o))

/- A local configuration is an object identity and a process. -/
structure local_config (β : Type) [objects α β]
    (self : class_name α) :=
  (σ : object_space β self)
  (m : process σ)
/- We fix a program, and global history. -/
variables (p : program α) (θ : global_history α β)
/- A step is taken on a local configuration. -/
def local_config.step : local_config β self →
    option ((local_config β self) × option (event α β)) :=
/- If the process is inactive, we obtain a pending method call. If no method call is pending, no step is taken. Otherwise, the next local configuration is an active process with the arguments of the selected method, a default store, and the body of the method as statement; additionally, an event is generated. -/
/- Otherwise, there is an active process. We look at the list of statements. If the list is empty, the process becomes inactive. -/
/- Otherwise, there is a current statement. If the current statement is an if statement, for which we evaluate the boolean pure expression. If it is true, we replace the current statement by those of the then-branch. Otherwise, we replace the current statement by those of the else-branch. -/
/- Otherwise, there is a while statement. We evaluate the boolean pure expression. If it is true, we prepend the body to the current statements. Otherwise, we discard the current statement. -/
/- Otherwise, we consider the assignment statement. We evaluate the pure expression, and the result is taken to update the variable on the left-hand side: if it is a field then the object space field state is updated, otherwise it is a local and the store is updated. In both cases, the current statement is discarded. -/
/- Otherwise, we have an async statement. We evaluate the argument list to a value list; the object pure expression is evaluated to an object value. If that value is null, no step is taken. Otherwise, we generate a method selection event with our object as caller and the appropriate call site, and discard the current statement. -/
/- Otherwise, we have an alloc statement. We evaluate the argument list to a value list. A fresh object identity is obtained from the global history. A method selection event to the constructor of the freshly obtained object is generated with an approriate call site, and the current statement is discarded. -/
  sorry

/- A global configuration is a finite set of object configurations and a global history. -/
structure global_config (α β : Type) [objects α β] :=
  (Γ (self : class_name α): finset (local_config β self))
  (θ: global_history α β)
