/- Copyright 2019 (c) Hans-Dieter Hiep. All rights reserved. Released under MIT license as described in the file LICENSE. -/

import objects

universe u

open objects list

/- An event is either an asynchronous method call of some caller object to a callee object, its method, and for each parameter an argument value. Or, an event is a method selection. -/
@[derive decidable_eq]
structure callsite (α β : Type) [objects α β] :=
  {c : class_name α}
  (o : {o : β // c = class_of α o})
  (m : method_name c)
  (τ : vallist (param_types m))
def callsite.elim {α β : Type} [objects α β] {γ : Sort u}
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
def event.to_callsite {α β : Type} [objects α β] :
    event α β → callsite α β
| (event.call _ c) := c
| (event.selection c) := c
def event.o {α β : Type} [objects α β] (e : event α β) :
  β := e.to_callsite.o
def event.c {α β : Type} [objects α β] (e : event α β) :
  class_name α := e.to_callsite.c
def event.m {α β : Type} [objects α β] (e : event α β) :
  method_name e.c := e.to_callsite.m
def event.τ {α β : Type} [objects α β] (e : event α β) :
  vallist (param_types e.m) := e.to_callsite.τ
instance event.event_to_callsite {α β : Type} [objects α β] :
  has_coe (event α β) (callsite α β) := ⟨event.to_callsite⟩

/- A global history is a sequence of events. -/
@[reducible]
def global_history (α β : Type) [objects α β] :=
  list (event α β)
/- There are two subsequences of a global history. The first consists only of call events with the object as callee (abstracted to its corresponding call site), the second consists only of selection events with the object as callee. -/
def event.is_call_to {α β : Type} [objects α β] (x : β) :
    event α β → option (callsite α β)
| (event.call _ c) := if x = c.o then some c else none
| _ := none
/- Call events to an object are of that object. -/
@[simp]
lemma event.is_call_to_object {α β : Type} [objects α β]
  {x : β} {e : event α β} {c : callsite α β} :
  event.is_call_to x e = some c → c.o.val = x :=
begin
  intro, cases e; simp [event.is_call_to] at a,
  { by_cases (x = e_a_1.o); simp [h] at a,
    simp [coe,lift_t,has_lift_t.lift] at h,
    simp [coe_t,has_coe_t.coe,coe_b,has_coe.coe] at h,
    rewrite h, rewrite ← a, exfalso, assumption },
  { exfalso, assumption }
end
def event.is_selection_of {α β : Type} [objects α β] (x : β) :
    event α β → option (callsite α β)
| (event.selection c) := if x = c.o then some c else none
| _ := none
/- Selection events of an object are of that object. -/
@[simp]
lemma event.is_selection_of_object {α β : Type} [objects α β]
  {x : β} {e : event α β} {c : callsite α β} :
  event.is_selection_of x e = some c → c.o.val = x :=
begin
  intro, cases e; simp [event.is_selection_of] at a,
  { exfalso, assumption },
  { by_cases (x = e.o); simp [h] at a,
    simp [coe,lift_t,has_lift_t.lift] at h,
    simp [coe_t,has_coe_t.coe,coe_b,has_coe.coe] at h,
    rewrite h, rewrite ← a, exfalso, assumption }
end
/- The subsequences are obtained by filtering out events. -/
def global_history.calls_to {α β : Type} [objects α β]
    (θ : global_history α β) (x : β) : list (callsite α β) :=
  θ.filter_map (event.is_call_to x)
def global_history.selections_of {α β : Type} [objects α β]
    (θ : global_history α β) (x : β) : list (callsite α β) :=
  θ.filter_map (event.is_selection_of x)
reserve notation `!`:68
reserve notation `?`:68
infix ! := global_history.calls_to
infix ? := global_history.selections_of
/- The list of pending calls to an object is the list of calls to, with the selections removed. -/
def global_history.pending_calls_to {α β : Type} [objects α β]
    (θ : global_history α β) (o : β) : list (callsite α β) := 
  (θ!o).remove_all (θ?o)
/- Pending calls have the same object as requested. -/
lemma global_history.pending_calls_to_object
  {α β : Type} [objects α β] (θ : global_history α β) (o : β) :
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
def global_history.sched {α β : Type} [objects α β]
    (θ : global_history α β) (o : β) : option (callsite α β) :=
  head (lift (θ.pending_calls_to o))
/- Scheduled calls have the same object as requested. -/
lemma global_history.sched_object {α β : Type} [objects α β]
  (θ : global_history α β) (o : β) (c : callsite α β) :
  (global_history.sched θ o) = some c → c.o.val = o :=
begin
  unfold global_history.sched,
  cases H : (global_history.pending_calls_to θ o),
  { intro, exfalso, apply head_lift_nil a },
  { intro, have : hd = c, apply tail_lift_some a,
    apply global_history.pending_calls_to_object θ,
    rewrite H, rewrite this, simp }
end
def global_history.collect {α β : Type} [objects α β]
    (θ : global_history α β) : finset β :=
  to_finset (foldr (λ(e : event α β) l, e.o :: l) [] θ)
def global_history.fresh {α β : Type} [objects α β]
    (o : β) (θ : global_history α β) : Prop :=
  o ∉ θ.collect
