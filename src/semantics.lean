-- (C) Copyright 2019, Hans-Dieter Hiep

import syntax

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
  (list_at.head .(x) .(xs)) := v
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
/- A local configuration is an object configuration and a process. -/
structure local_config (α β : Type) [objects α β] :=
  (self : class_name α)(this : object_space β self)
  (m : process this)
/- A global history is a sequence of events. An event is either an asynchronous method call of some caller object to a callee object, its method, and for each parameter an argument value. Or, an event is a method selection. -/
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
/- Given an object, we consider two subsequences of a global history. The first consists only of call events with the object as callee (abstracted to its corresponding call site), the second consists only of selection events with the object as callee. -/
@[simp]
def event.is_call_to (α : Type) [objects α β] (x : β) :
    event α β → option (callsite α β)
| (event.call _ c) := if x = c.o then some c else none
| _ := none
@[simp]
def event.is_selection_of (α : Type) [objects α β] (x : β) :
    event α β → option (callsite α β)
| (event.selection c) := if x = c.o then some c else none
| _ := none
@[simp]
def event.calls_to (x : list (event α β)) (o : β) :
    list (callsite α β) :=
  x.filter_map (event.is_call_to α o)
notation x `!`:68 o:69 := event.calls_to x o
@[simp]
def event.selections_of (x : list (event α β))
    (o : β) : list (callsite α β) :=
  x.filter_map (event.is_selection_of α o)
notation x `?`:68 o:69 := event.selections_of x o
/- A global history is a sequence of events, restricted to those in which for each object, the subsequence of calls to is a prefix of the subsequence of selections. -/
@[reducible]
def global_history (α β : Type) [objects α β] :=
  {seq : list (event α β) // ∀ o : β, is_prefix (seq?o) (seq!o)}
/- Given a global history and an object, a call site is pending if the number of occurrences in calls is higher than the number of occurrences in selections. -/
def global_history.is_pending (θ : global_history α β)
    (c : callsite α β) : Prop :=
  length (filter (= c) (θ?c.o)) >
  length (filter (= c) (θ!c.o))
/- Given a non-empty global history, a selection event is never first. -/
lemma global_history.never_selection (seq : list (event α β))
  (c : callsite α β) : ¬∀ o : β, is_prefix
  ((event.selection c::seq)?o) ((event.selection c::seq)!o) :=
begin
  admit -- TODO
end
/- Given a global history and an object identity, a scheduler scheduler takes the first pending call, if any. To do so we match each call event with the first corresponding selection event, cancelling them if they both occur. If no corresponding selection event is found, we have found a pending call. -/
def global_history.cancel: callsite α β → list (event α β) →
    option (list (event α β))
| _ [] := none
| c (d :: l) := if c = d then (some l)
    else option.map (cons d) (global_history.cancel c l)
-- TODO: proof that global_history.cancel can be lifted to global histories
def global_history.sched : global_history α β → β →
    option (callsite α β)
| ⟨[], _⟩ _ := none
| ⟨(event.selection c) :: l, H⟩ o' :=
  begin
    exfalso, apply global_history.never_selection l c, apply H
  end
| ⟨e@(event.call o _) :: l, _⟩ o' :=
  match global_history.cancel ↑e l with
  | none := e
  | (some l') := sorry -- global_history.sched l'
  end
/- A local step is taken on a local configuration and a corresponding local history, to a next local configuration. -/
def local_step (x : local_config α β) : local_config α β :=
  sorry
/- A global configuration is a finite set of object configurations and a global history. -/
structure global_config (α β : Type) [objects α β] :=
  (Γ: finset (local_config α β))
  (θ: global_history α β)
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
  filter (event.is_local_to α o) θ
