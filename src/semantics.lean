-- (C) Copyright 2019, Hans-Dieter Hiep

import syntax data.finsupp

universe u

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
inductive value [objects α β] : type α → Type 1
| object {c : class_name α} (o : β)
    (H : c = class_of α o) : value (ref c)
| null (c : class_name α) : value (ref c)
| term {γ : datatype} : γ → value (data α γ)
instance value.inhabited [objects α β] :
    Π{ty : type α}, inhabited (value ty)
| (ref c) := ⟨value.null c⟩
| (data .(α) γ) := ⟨value.term γ.default⟩
-- Projection of value to term
def value.unterm [objects α β] {γ : datatype} :
    Π (x : value (data α γ)), γ.host
| (value.term t) := t
-- Projection of value to object
def value.unobject {c : class_name α} :
    Π (x : value (ref c)), option β
| (value.object o _) := o
| (value.null _) := none
def value.not_null [objects α β] {c : class_name α} (x : value (ref c)) : Prop := x ≠ value.null c
-- Projection of value to object (guarantee)
def value.the_object {c : class_name α} :
    Π (x : value (ref c)), value.not_null x → β
| (value.object o _) _ := o
| (value.null .(c)) G := begin exfalso, apply G, refl end
lemma value.class_of_the_object [objects α β] {c : class_name α}
  {x : value (ref c)} (G : value.not_null x) :
  class_of α (value.the_object x G) = c :=
begin
  cases x,
  {unfold value.the_object, apply eq.symm, assumption},
  {exfalso, apply G, refl}
end

/- For class C we have a state space Σ(C) consisting of a this identity and an assignment of fields to values. For method m, we have a argument space Σ(m) consisting of an assignment of method parameters to values. -/
@[derive decidable_eq]
structure arg_space [objects α β]
    {self : class_name α} (m : method_name self) :=
  (map (p : param_name m) : value (param_type p))
structure state_space [objects α β] (self : class_name α) :=
  (map (f : field_name self) : value (field_type f))
  (this : value (ref self))
  (H : value.not_null this)
def state_space.id [objects α β] {self : class_name α}
  (σ : state_space self) : β := value.the_object σ.this σ.H
lemma state_space.class_of_id [objects α β] {self : class_name α}
  (σ : state_space self) : class_of α σ.id = self :=
begin
  unfold state_space.id, apply value.class_of_the_object
end
notation Σ(m) := arg_space m
notation Σ(C) := state_space C

/- Given a list of types, we have a value list of values with matching types. -/
inductive vallist [objects α β] : list (type α) → Type 1
| nil : vallist []
| cons {ty : type α} {l : list (type α)} :
  value ty → vallist l → vallist (ty::l)
def vallist.default [objects α β] :
    Π(l : list (type α)), vallist l
| [] := vallist.nil
| (t :: l) := vallist.cons (default (value t))
    (vallist.default l)
instance vallist.inhabited [objects α β] (l : list (type α)) :
  inhabited (vallist l) := ⟨vallist.default l⟩
/- Given a value list and an index in the list of types, we obtain a value. -/
def vallist.lookup [objects α β] {ty : type α} :
    Π {l : context α}, vallist l → list_at ty l → value ty
| (x :: xs) (vallist.cons (v : value x) _)
  (list_at.here .(x) .(xs)) := v
| (x :: xs) (vallist.cons _ (ys : vallist xs))
  (list_at.tail .(x) (zs : list_at .(ty) xs)) :=
    vallist.lookup ys zs

variables {C : class_name α} {e : tenv C}

/- An active process consists of: an argument space (of the current method), a value list (of the local variables), and a list of statements. -/
structure active_process (e : tenv C) :=
  (args : Σ(e.current)) (store : vallist e.locals)
  (body : list (statement e))
/- Given an object space and active process, we can lookup the value of a read variable. -/
def active_process.lookup (π : active_process e) (σ : Σ(C))
    {tx : type α} : rvar e tx → value tx
| (rvar.tvar t) := eq.mpr (congr_arg _ t.H) $ σ.this
| (rvar.fvar f) := eq.mpr (congr_arg _ f.H) $ σ.map f.idx
| (rvar.pvar p) := eq.mpr (congr_arg _ p.H) $ π.args.map p.idx
| (rvar.lvar l) := π.store.lookup l.idx
/- Evaluating a pure expression, Val(p)(σ,π). -/
def eval (σ : Σ(C)) (π : active_process e) :
    Π {ty : type α}, pexp e ty → value ty
| bool (requal l r) := value.term $ to_bool (eval l = eval r)
| _ (lookup r) := π.lookup σ r
| _ (const _ v) := value.term v
| _ (apply f r) := value.term $ f (eval r).unterm
/- A process is either nil or an active process. -/
inductive process {α : Type} [objects α β] (C : class_name α)
| nil : process
| active (e : tenv C) (a : active_process e) : process

/- An event is either an asynchronous method call of some caller object to a callee object, its method, and for each parameter an argument value. Or, an event is a method selection. -/
@[derive decidable_eq]
structure callsite (α β : Type) [objects α β] :=
  (o : β)
  (m : method_name (class_of α o))
  (τ : Σ(m))
def callsite.elim {γ : Sort u} (c : callsite α β)
    (f : Π(o : β) (m : method_name (class_of α o)) (τ : Σ(m)),
      c = ⟨o,m,τ⟩ → γ) : γ :=
  match c, rfl : (∀ b, c = b → γ) with
  | ⟨o,m,τ⟩, h := f o m τ h
  end

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
def event.is_call_to {α : Type} [objects α β] (x : β) :
    event α β → option (callsite α β)
| (event.call _ c) := if x = c.o then some c else none
| _ := none
/- Call events to an object are of that object. -/
@[simp]
lemma event.is_call_to_object {x : β} {e : event α β}
  {c : callsite α β} : event.is_call_to x e = some c →
  c.o = x :=
begin
  intro, cases e; simp [event.is_call_to] at a,
  { by_cases (x = e_a_1.o); simp [h] at a,
    rewrite h, rewrite ← a, exfalso, assumption },
  { exfalso, assumption }
end
def event.is_selection_of {α : Type} [objects α β] (x : β) :
    event α β → option (callsite α β)
| (event.selection c) := if x = c.o then some c else none
| _ := none
/- Selection events of an object are of that object. -/
@[simp]
lemma event.is_selection_of_object {x : β} {e : event α β}
  {c : callsite α β} : event.is_selection_of x e = some c →
  c.o = x :=
begin
  intro, cases e; simp [event.is_selection_of] at a,
  { exfalso, assumption },
  { by_cases (x = e.o); simp [h] at a,
    rewrite h, rewrite ← a, exfalso, assumption }
end
/- The subsequences are obtained by filtering out events. -/
def global_history.calls_to (θ : global_history α β)
    (x : β) : list (callsite α β) :=
  θ.filter_map (event.is_call_to x)
def global_history.selections_of (θ : global_history α β)
    (x : β) : list (callsite α β) :=
  θ.filter_map (event.is_selection_of x)
reserve notation `!`:68
reserve notation `?`:68
infix ! := global_history.calls_to
infix ? := global_history.selections_of
/- The list of pending calls to an object is the list of calls to, with the selections removed. -/
def global_history.pending_calls_to (θ : global_history α β)
  (o : β) : list (callsite α β) := (θ!o).remove_all (θ?o)
/- Pending calls have the same object as requested. -/
lemma global_history.pending_calls_to_object
  (θ : global_history α β) (o : β) :
  ∀ c : callsite α β,
    c ∈ (global_history.pending_calls_to θ o) → c.o = o :=
begin
  unfold global_history.pending_calls_to, intro,
  suffices : c ∈ θ!o → c.o = o, intro, apply this,
  simp [remove_all] at a, cases a, assumption,
  simp [global_history.calls_to], intro, intro,
  apply event.is_call_to_object
end
/- We have an optional first pending call to an object. -/
def global_history.sched (θ : global_history α β)
    (o : β) : option (callsite α β) :=
  head (lift (θ.pending_calls_to o))
/- Scheduled calls have the same object as requested. -/
lemma global_history.sched_object (θ : global_history α β)
  (o : β) (c : callsite α β) :
  (global_history.sched θ o) = some c → c.o = o :=
begin
  unfold global_history.sched,
  cases H : (global_history.pending_calls_to θ o),
  { intro, exfalso, apply head_lift_nil a },
  { intro, have : hd = c, apply tail_lift_some a,
    apply global_history.pending_calls_to_object θ,
    rewrite H, rewrite this, simp }
end

/- We fix a program, and global history. -/
variables (p : program α) (θ : global_history α β)
/- A local configuration is an object identity and a process. -/
structure local_config (β : Type) [objects α β]
  (C : class_name α) := (σ : Σ(C)) (m : process C)
/- Given a method and arguments, we can activate a process. -/
def process.activate (C : class_name α) (m : method_name C)
    (τ : Σ(m)) : process C :=
  process.active (p.body m).tenv ⟨τ,default _,(p.body m).S⟩

/- A step is taken on a local configuration. -/
def local_config.step : local_config β C → option ((local_config β C) × option (event α β))
    
/- If the process is inactive, we obtain a pending method call. If no method call is pending, no step is taken. Otherwise, the next local configuration is an active process with the arguments of the selected method, a default store, and the body of the method as statement; additionally, a selection event is generated. -/
| ⟨σ, process.nil .(C)⟩ := let c := θ.sched σ.id in
    option.elim c (λh, none) (λd h, callsite.elim d (λo m τ g,
      let p := process.activate p (class_of α o) m τ,
        H : class_of α o = C := begin
          have : (θ.sched σ.id) = some ⟨o, m, τ⟩,
            rw ← g, assumption,
          have : state_space.id σ = o,
            apply eq.symm,
            apply global_history.sched_object θ (σ.id) ⟨o,m,τ⟩,
            assumption,
          rewrite ← this,
          apply state_space.class_of_id
        end
      in some ⟨⟨σ, cast (congr_arg _ H) p⟩, event.selection d⟩))
/- Otherwise, there is an active process. We look at the list of statements. If the list is empty, the process becomes inactive. -/
/- Otherwise, there is a current statement. If the current statement is an if statement, for which we evaluate the boolean pure expression. If it is true, we replace the current statement by those of the then-branch. Otherwise, we replace the current statement by those of the else-branch. -/
/- Otherwise, there is a while statement. We evaluate the boolean pure expression. If it is true, we prepend the body to the current statements. Otherwise, we discard the current statement. -/
/- Otherwise, we consider the assignment statement. We evaluate the pure expression, and the result is taken to update the variable on the left-hand side: if it is a field then the object space field state is updated, otherwise it is a local and the store is updated. In both cases, the current statement is discarded. -/
/- Otherwise, we have an async statement. We evaluate the argument list to a value list; the object pure expression is evaluated to an object value. If that value is null, no step is taken. Otherwise, we generate a method selection event with our object as caller and the appropriate call site, and discard the current statement. -/
/- Otherwise, we have an alloc statement. We evaluate the argument list to a value list. A fresh object identity is obtained from the global history. A method selection event to the constructor of the freshly obtained object is generated with an approriate call site, and the current statement is discarded. -/

/- A global configuration is a finite set of object configurations and a global history. -/
structure global_config (α β : Type) [objects α β] :=
  (Γ (self : class_name α): finset (local_config β self))
  (θ: global_history α β)

-- TODO: move to some other place
/- A local history is obtained from a global history and an object identity: it consists of the outgoing calls, an method selections involving the object. -/
@[reducible]
def event.is_local_to (α : Type) [objects α β] (x : β) :
    event α β → Prop
| (event.call y _) := x = y -- same caller
| (event.selection c) := x = c.o -- same callee
instance event.decidable_local (o : β) (e: event α β) :
    decidable (event.is_local_to α o e) :=
  begin cases e; apply_instance end
def local_history (θ : global_history α β) (x : β) :=
  θ.filter (event.is_local_to α x)
