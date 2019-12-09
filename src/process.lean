/- Copyright 2019 (c) Hans-Dieter Hiep. All rights reserved. Released under MIT license as described in the file LICENSE. -/

import history

universe u

open objects interpret

/- For class C we have a state space Σ(C) consisting of a this identity and an assignment of fields to values. -/
@[derive decidable_eq]
structure state_space {α β : Type} [objects α β]
    (self : class_name α) :=
  (map (f : field_name self) : value (field_type f))
  (this : value (type.ref self))
  (N : value.not_null this)
def state_space.id {α β : Type} [objects α β]
    {self : class_name α} (σ : state_space self) : β :=
  value.the_object σ.N
lemma state_space.class_of_id {α β : Type} [objects α β]
  {self : class_name α} (σ : state_space self) :
  class_of α σ.id = self :=
begin
  unfold state_space.id, apply value.class_of_the_object
end
/- A state space can be updated. -/
def state_space.update {α β : Type} [objects α β]
    {C : class_name α} (f : field_name C)
    (v : value (field_type f)) : state_space C → state_space C
| ⟨map, this, N⟩ := ⟨λg, if H : f = g
    then cast begin rewrite H end v else map g,this,N⟩
/- A state space can be updated, given a field variable in a typing environment related to the same class. -/
def state_space.updatev {α β : Type} [objects α β]
    {C : class_name α} {e : tenv C} {ty : type α}
    (fvar : fvar e ty) (v : value ty)
    (σ : state_space C) : state_space C :=
  σ.update fvar.idx (cast begin rewrite fvar.H end v)
notation Σ(C) := state_space C

/- An active process consists of: a value list (of the arguments of the current method), a value list (of the local variables), and a list of statements. -/
@[derive decidable_eq]
structure active_process {α β : Type} [objects α β]
    (C : class_name α) :=
  (e : tenv C)
  (args : vallist e.args) (store : vallist e.locals)
  (body : list (statement e))
/- Given a state and active process, we can lookup the value of a read variable. -/
def active_process.lookup {α β : Type} [objects α β]
    {C : class_name α}
    (σ : Σ(C)) (π : active_process C)
    {tx : type α} : rvar π.e tx → value tx
| (rvar.tvar t) := cast begin rewrite t.H end σ.this
| (rvar.fvar f) := cast begin rewrite f.H end $ σ.map f.idx
| (rvar.pvar p) := π.args.lookup p.idx
| (rvar.lvar l) := π.store.lookup l.idx

/- A process is either nil or an active process. -/
@[derive decidable_eq]
inductive process {α β : Type} [objects α β] (C : class_name α)
| nil : process
| active (a : active_process C) : process

/- Evaluating a pure expression to a list of values. -/
def eval {α β : Type} [interpret α β]
    {C : class_name α}
    (σ : Σ(C)) (π : active_process C) :
    Π {l : list (type α)}, pexp π.e l → vallist l
| _ (pexp.const .(π.e) sym) := vallist.single $
    (interp sym) vallist.nil
| _ (pexp.app f r) := vallist.single $
    (interp f) (eval r)
| _ (pexp.lookup r) := vallist.single (π.lookup σ r)
| _ (pexp.equal l r) := vallist.single $ value.term $
    cast data_type_booleanr $ to_bool (eval l = eval r)
| _ (pexp.cons h t) := vallist.consl (eval h) (eval t)

/- Given a method and arguments, we can activate a process. -/
def process.activate {α β : Type} [objects α β]
    (p : program α) (c : class_name α) (m : method_name c)
    (τ : vallist (param_types m)) : process c :=
  process.active ⟨(p.body m).tenv,τ,default _,(p.body m).S⟩

def process.schedule {α β : Type} [interpret α β]
    (pr : program α) {θ : global_history α β}
    {C : class_name α} (σ : Σ(C)) (d : callsite α β)
    (H : global_history.sched θ (state_space.id σ) = some d)
    : process C :=
  callsite.elim d (λc o m τ g,
    let p := process.activate pr c m τ,
      G : process c = process C := begin
        have F : state_space.id σ = o.val,
          apply eq.symm,
          apply global_history.sched_object θ (σ.id) ⟨o,m,τ⟩,
          rw ← g, apply H,
        rewrite o.property,
        rewrite ← F,
        rewrite state_space.class_of_id
      end
    in cast G p)
