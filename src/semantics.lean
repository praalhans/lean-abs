/- Copyright 2019 (c) Hans-Dieter Hiep. All rights reserved. Released under MIT license as described in the file LICENSE. -/

import syntax data.finsupp data.fintype

universe u

open signature nat list

/- Fix a signature. We consider an interpretation of reference types and data types. Reference types are interpreted as object identities. Each object identity is associated to a single class name. Given a finite set of object identities, there can always be a fresh object identity not in that set (thanks to Johannes Hölzl). Allocation of a fresh object results in an object with the same class name as allocated. Equality is decidable for objects. Each record name is uniquely associated to a data type. A data type comprises an inhabited Lean type with decidable equality. The built-in boolean is associated to Lean's bool with false as default. -/
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
(alloc: finset β → class_name α → β)
(class_of: β → class_name α)
(decidable_object: decidable_eq β)
(alloc_is_new (x : finset β) (c : class_name α):
  (alloc x c) ∉ x)
(alloc_class_of (x : finset β) (c : class_name α):
  class_of (alloc x c) = c)
(data_type: record_name α → datatype)
(data_type_boolean:
  (data_type (boolean_name α)).host = bool)
(data_type_boolean_inhabited:
  (cast data_type_boolean (data_type (boolean_name α))
    .inhabited_host.default) = ff)
open objects

variables {α β : Type} [objects α β]
variable {c : class_name α}

lemma data_type_booleanr [objects α β] :
  bool = (data_type (boolean_name α)).host :=
begin symmetry, apply data_type_boolean end
instance objects.decidable_eq : decidable_eq β :=
  decidable_object α β

/- We treat values as being of a type. A value of a reference type is an object of the same class, or null. A value of a data type is a term of the associated type in Lean. -/
@[derive decidable_eq]
inductive value [objects α β] : type α → Type 1
| object {c : class_name α} :
    {o : β // c = class_of α o} → value (type.ref c)
| null (c : class_name α) :
    value (type.ref c)
| term {r : record_name α} :
    (data_type r).host → value (type.data r)
/- The default value of a reference type is null, and the default value of a data type is the default in Lean. -/
instance value.inhabited [objects α β] :
    Π{ty : type α}, inhabited (value ty)
| (type.ref c) := ⟨value.null c⟩
| (type.data r) := ⟨value.term (data_type r).default⟩
-- Projection of value to term
def value.unterm [objects α β] {r : record_name α} :
    Π (x : value (type.data r)), (data_type r).host
| (value.term t) := t
-- Projection of boolean value to bool
def value.unbool [objects α β] :
  Π (x : value (boolean α)), bool
| (value.term t) := cast (data_type_boolean α β) t
-- Projection of value to potential object
def value.unobject {c : class_name α} :
    Π (x : value (type.ref c)), option β
| (value.object o) := o
| (value.null _) := none
def value.not_null [objects α β] {c : class_name α}
  (x : value (type.ref c)) : Prop := x ≠ value.null c
-- Projection of not-null value to object identity
def value.the_object {c : class_name α} :
    Π (x : value (type.ref c)), value.not_null x → β
| (value.object o) _ := o
| (value.null .(c)) G := begin exfalso, apply G, refl end
lemma value.class_of_the_object [objects α β] {c : class_name α}
  {x : value (type.ref c)} (G : value.not_null x) :
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
def value.elim_object {γ : Sort u} {c : class_name α}
    (v : value (type.ref c))
    (f : Π(o : {o : β // c = class_of α o}),
      v = value.object o → γ) (g : v = value.null c → γ) : γ :=
  match v, rfl : (∀ b, v = b → γ) with
  | (value.object o), h := f o h
  | (value.null .(c)), h := g h
  end

/- Given a list of types, we have a value list of values with matching types. -/
@[derive decidable_eq]
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
/- A value list of a single type is just a value. -/
def vallist.single [objects α β] {ty : type α}
    (v : value ty) : vallist [ty] :=
  vallist.cons v vallist.nil
/- There is a unique value of a single value list. -/
def vallist.the [objects α β] {ty : type α} :
    vallist [ty] → value ty
| (vallist.cons h vallist.nil) := h
/- A value list of a single type can be appended at the front to form a new value list. -/
def vallist.consl [objects α β]
    {ty : type α} {l : list (type α)}
    (h : vallist [ty]) (t : vallist l) : vallist (ty :: l) :=
  vallist.cons (h.the) t
/- Given a value list and an index in the list of types, we obtain a value. -/
def vallist.lookup [objects α β] {ty : type α} :
    Π {l : context α}, vallist l → list_at ty l → value ty
| (x :: xs) (vallist.cons v _) (list_at.here .(x) .(xs)) := v
| (x :: xs) (vallist.cons _ ys) (list_at.tail .(x) zs) :=
    vallist.lookup ys zs

/- For class C we have a state space Σ(C) consisting of a this identity and an assignment of fields to values. -/
@[derive decidable_eq]
structure state_space [objects α β] (self : class_name α) :=
  (map (f : field_name self) : value (field_type f))
  (this : value (type.ref self))
  (N : value.not_null this)
def state_space.id [objects α β] {self : class_name α}
  (σ : state_space self) : β := value.the_object σ.this σ.N
lemma state_space.class_of_id [objects α β]
  {self : class_name α} (σ : state_space self) :
  class_of α σ.id = self :=
begin
  unfold state_space.id, apply value.class_of_the_object
end
notation Σ(C) := state_space C

/- A heap is a finite set of state spaces. TODO -/

/- An event is either an asynchronous method call of some caller object to a callee object, its method, and for each parameter an argument value. Or, an event is a method selection. -/
@[derive decidable_eq]
structure callsite (α β : Type) [objects α β] :=
  {c : class_name α}
  (o : {o : β // c = class_of α o})
  (m : method_name c)
  (τ : vallist (param_types m))
def callsite.elim {γ : Sort u}
    (cs : callsite α β) (f : Π{c : class_name α}
      (o : {o : β // c = class_of α o})
      (m : method_name c) (τ : vallist (param_types m)),
      cs = @callsite.mk α β _ c o m τ → γ) : γ :=
  match cs, rfl : (∀ b, cs = b → γ) with
  | ⟨o,m,τ⟩, h := f o m τ h
  end

@[derive decidable_eq]
inductive event (α β : Type) [objects α β]
| call: β → callsite α β → event
| selection: callsite α β → event
def event.to_callsite : event α β → callsite α β
| (event.call _ c) := c
| (event.selection c) := c
def event.o (e : event α β) : β := e.to_callsite.o
def event.c (e : event α β) : class_name α := e.to_callsite.c
def event.m (e : event α β) : method_name e.c := e.to_callsite.m
def event.τ (e : event α β) : vallist (param_types e.m) :=
  e.to_callsite.τ
instance event.event_to_callsite : has_coe (event α β)
  (callsite α β) := ⟨event.to_callsite⟩

/- A global history is a sequence of events. -/
@[reducible]
def global_history (α β : Type) [objects α β] :=
  list (event α β)
/- There are two subsequences of a global history. The first consists only of call events with the object as callee (abstracted to its corresponding call site), the second consists only of selection events with the object as callee. -/
def event.is_call_to {α : Type} [objects α β] (x : β) :
    event α β → option (callsite α β)
| (event.call _ c) := if x = c.o then some c else none
| _ := none
/- Call events to an object are of that object. -/
@[simp]
lemma event.is_call_to_object {x : β} {e : event α β}
  {c : callsite α β} : event.is_call_to x e = some c →
  c.o.val = x :=
begin
  intro, cases e; simp [event.is_call_to] at a,
  { by_cases (x = e_a_1.o); simp [h] at a,
    simp [coe,lift_t,has_lift_t.lift] at h,
    simp [coe_t,has_coe_t.coe,coe_b,has_coe.coe] at h,
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
  c.o.val = x :=
begin
  intro, cases e; simp [event.is_selection_of] at a,
  { exfalso, assumption },
  { by_cases (x = e.o); simp [h] at a,
    simp [coe,lift_t,has_lift_t.lift] at h,
    simp [coe_t,has_coe_t.coe,coe_b,has_coe.coe] at h,
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
    c ∈ (global_history.pending_calls_to θ o) → c.o.val = o :=
begin
  unfold global_history.pending_calls_to, intro,
  suffices : c ∈ θ!o → c.o.val = o, intro, apply this,
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
  (global_history.sched θ o) = some c → c.o.val = o :=
begin
  unfold global_history.sched,
  cases H : (global_history.pending_calls_to θ o),
  { intro, exfalso, apply head_lift_nil a },
  { intro, have : hd = c, apply tail_lift_some a,
    apply global_history.pending_calls_to_object θ,
    rewrite H, rewrite this, simp }
end
def global_history.collect
    (θ : global_history α β) : finset β :=
  to_finset (foldr (λ(e : event α β) l, e.o :: l) [] θ)
def global_history.fresh (θ : global_history α β)
    (c : class_name α) : {o : β // c = class_of α o} :=
  let o := alloc (θ.collect) c,
    H : c = class_of α o := begin
      apply eq.symm, apply alloc_class_of end
  in ⟨o,H⟩

/- An active process consists of: an argument space (of the current method), a value list (of the local variables), and a list of statements. -/
variables {C : class_name α} {e : tenv C}
structure active_process (e : tenv C) :=
  (args : vallist e.args) (store : vallist e.locals)
  (body : list (statement e))

/- Given an object space and active process, we can lookup the value of a read variable. -/
def active_process.lookup (σ : Σ(C)) (π : active_process e)
    {tx : type α} : rvar e tx → value tx
| (rvar.tvar t) := cast begin rewrite t.H, refl end σ.this
| (rvar.fvar f) := cast begin rewrite f.H end $ σ.map f.idx
| (rvar.pvar p) := π.args.lookup p.idx
| (rvar.lvar l) := π.store.lookup l.idx
/- Evaluating a pure expression to a list of values. -/
def eval (σ : Σ(C)) (π : active_process e) :
    Π {l : list (type α)}, pexp e l → vallist l
| _ (pexp.requal l r) := vallist.single $ value.term $
    cast data_type_booleanr $ to_bool (eval l = eval r)
| _ (pexp.lookup r) := vallist.single (π.lookup σ r)
| _ (pexp.const .(e) s) := _
| _ (pexp.app f r) := _
| _ (pexp.cons h t) := vallist.consl (eval h) (eval t)

/- A state space can be updated. -/
def state_space.update
    (f : field_name C) (v : value (field_type f)) :
    state_space C → state_space C
| ⟨map, this, N⟩ := ⟨λg, if H : f = g
    then cast begin rewrite H end v else map g,this,N⟩
/- A state space can be updated, given a field variable in a typing environment related to the same class. -/
def state_space.updatev {ty : type α}
    (fvar : fvar e ty) (v : value ty) (σ : Σ(C)) : Σ(C) :=
  σ.update fvar.idx (cast begin rewrite fvar.H end v)
/- Given a value list and an index and a new value, we obtain a new value list which updates the given index. -/
def vallist.update [objects α β] {ty : type α} :
    Π {l : context α}, vallist l → list_at ty l →
    value ty → vallist l
| (x :: xs) (vallist.cons _ tl) (list_at.here .(x) .(xs)) v :=
    vallist.cons v tl
| (x :: xs) (vallist.cons v ys) (list_at.tail .(x) zs) w :=
    vallist.cons v (vallist.update ys zs w)

/- We fix a program, and global history. -/
variables (p : program α) (θ : global_history α β)
/- A process is either nil or an active process. -/
inductive process {α : Type} [objects α β] (C : class_name α)
| nil : process
| active (env : tenv C) (a : active_process env) : process
/- Given a method and arguments, we can activate a process. -/
def process.activate (C : class_name α) (m : method_name C)
    (τ : vallist (param_types m)) : process C :=
  process.active (p.body m).tenv ⟨τ,default _,(p.body m).S⟩
/- A local configuration is an object and its process. -/
structure local_config (α β : Type) [objects α β] :=
  (C : class_name α) (σ : Σ(C)) (m : process C)

/- A local result is the result of taking a step at a local configuration. -/
inductive local_result (α β : Type) [objects α β]
| crash: local_result
| no_step: local_result
| internal_step: local_config α β → local_result
| external_step: local_config α β → event α β → local_result

open local_result

/- A step is taken on a local configuration. -/
def local_config.step : local_config α β → local_result α β
/- If the process is inactive, we obtain a pending method call. If no method call is pending, no step is taken. Otherwise, the next local configuration is an active process with the arguments of the selected method, a default store, and the body of the method as statement; additionally, a selection event is generated. -/
| ⟨C, σ, process.nil _⟩ := let e := θ.sched σ.id in
    option.elim e
      (λ_, no_step α β)
      (λd h, callsite.elim d (λc o m τ g,
      let p := process.activate p c m τ,
        G : process c = process C := begin
          have : (θ.sched σ.id) = some ⟨o, m, τ⟩,
            rw ← g, assumption,
          have : state_space.id σ = o,
            apply eq.symm,
            apply global_history.sched_object θ (σ.id) ⟨o,m,τ⟩,
            assumption,
          rewrite o.property,
          simp [coe,lift_t,has_lift_t.lift] at this,
          simp [coe_t,has_coe_t.coe,coe_b,has_coe.coe] at this,
          rewrite ← this,
          rewrite state_space.class_of_id
        end
      in external_step ⟨C, σ, cast G p⟩ (event.selection d)))
/- Otherwise, there is an active process. We look at the list of statements. If the list is empty, the process becomes inactive. -/
| ⟨C, σ, process.active _ ⟨τ,ℓ,nil⟩⟩ :=
    internal_step ⟨C, σ, process.nil _⟩
/- Otherwise, there is a current statement. If the current statement is an if statement, for which we evaluate the boolean pure expression. If it is true, we replace the current statement by those of the then-branch. Otherwise, we replace the current statement by those of the else-branch. -/
| ⟨C, σ, process.active env
      π@⟨τ,ℓ,(stmt.ite p thenb elseb :: t)⟩⟩ :=
    internal_step $ match (eval σ π p).the.unbool with
    | tt := ⟨C, σ, process.active env
        ⟨τ,ℓ,stmt.to_list thenb ++ t⟩⟩
    | ff := ⟨C, σ, process.active env
        ⟨τ,ℓ,stmt.to_list elseb ++ t⟩⟩
    end
/- Otherwise, there is a while statement. We evaluate the boolean pure expression. If it is true, we prepend the body to all statements, before but including the current while statement. Otherwise, we discard the current statement. -/
| ⟨C, σ, process.active env π@⟨τ,ℓ,S@(stmt.while p dob :: t)⟩⟩ :=
    internal_step $ match (eval σ π p).the.unbool with
    | tt := ⟨C, σ, process.active env
        ⟨τ,ℓ,stmt.to_list dob ++ S⟩⟩
    | ff := ⟨C, σ, process.active env ⟨τ,ℓ,t⟩⟩
    end
/- Otherwise, we consider the assignment statement. We evaluate the pure expression, and the result is taken to update the variable on the left-hand side: if it is a field then the object space field state is updated, otherwise it is a local and the store is updated. In both cases, the current statement is discarded. -/
| ⟨C, σ, process.active env
      π@⟨τ,ℓ,(stmt.assign (svar.fvar f) p :: t)⟩⟩ :=
    internal_step ⟨C, σ.updatev f (eval σ π p).the,
      process.active env ⟨τ,ℓ,t⟩⟩
| ⟨C, σ, process.active env
      π@⟨τ,ℓ,(stmt.assign (svar.lvar ⟨l⟩) p :: t)⟩⟩ :=
    internal_step ⟨C, σ, process.active env
      ⟨τ,ℓ.update l (eval σ π p).the,t⟩⟩
/- Otherwise, we have an async statement. We evaluate the argument list to a value list; the object pure expression is evaluated to an object value. If that value is null, no step is taken. Otherwise, we generate a method selection event with our object as caller and the appropriate call site, and discard the current statement. -/
| ⟨C, σ, process.active env
      π@⟨τ,ℓ,(stmt.async c m G o τ' :: t)⟩⟩ :=
    (π.lookup σ o).elim_object
      (λo h, external_step ⟨C, σ, process.active env ⟨τ,ℓ,t⟩⟩
        (event.call σ.id ⟨o,m,eval σ π τ'⟩))
      (λ_, crash α β)
/- Otherwise, we have an alloc statement. We evaluate the argument list to a value list. A fresh object identity is obtained from the global history, and stored in the variable. A call event to the constructor of the freshly obtained object is generated with an approriate call site, and the current statement is discarded. -/
| ⟨C, σ, process.active env
      π@⟨τ,ℓ,(stmt.alloc c (svar.fvar f) τ' :: t)⟩⟩ :=
    let o := θ.fresh c, new := value.object o in
      external_step ⟨C, σ.updatev f new,
        process.active env ⟨τ,ℓ,t⟩⟩
        (event.call σ.id ⟨o,ctor c,eval σ π τ'⟩)
| ⟨C, σ, process.active env
      π@⟨τ,ℓ,(stmt.alloc c (svar.lvar ⟨l⟩) τ' :: t)⟩⟩ :=
    let o := θ.fresh c, new := value.object o in
      external_step ⟨C, σ,
        process.active env ⟨τ,ℓ.update l new,t⟩⟩
        (event.call σ.id ⟨o,ctor c,eval σ π τ'⟩)

/- A global configuration is a finite set of object configurations and a global history. -/
@[derive decidable_eq]
structure global_config (α β : Type) [objects α β] :=
  (Γ: finset (local_config α β))
  (θ: global_history α β)
/- A step is taken on a global configuration. -/
def global_config.step : global_config α β →
  finset (global_config α β)
| ⟨Γ, θ⟩ := Γ.bind (λl : local_config α β,
    match l.step p θ with
    | crash .(α) .(β) := _
    | no_step .(α) .(β) := ∅ 
    | (internal_step l') := _
    | (external_step l' e) := _
    end)
