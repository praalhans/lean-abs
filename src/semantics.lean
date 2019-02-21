/- Copyright 2019 (c) Hans-Dieter Hiep. All rights reserved. Released under MIT license as described in the file LICENSE. -/

import process

/- A local configuration is an object and its process. -/
@[derive decidable_eq]
structure local_config (α β : Type) [interpret α β]
  (C : class_name α) := (σ : Σ(C)) (m : process C)
/- A global configuration is a finite set of object configurations and a global history. -/
@[derive decidable_eq]
structure global_config (α β : Type) [interpret α β] :=
  --(Γ: finset (local_config α β))
  (θ: global_history α β)

/- A step is taken on a local configuration. -/
def local_config.step {α β : Type} [interpret α β]
    (p : program α) (C : class_name α)
    (θ : global_history α β) :
    local_config α β C → set (local_config α β C)
/- If the process is inactive, we obtain a pending method call. If no method call is pending, no step is taken. Otherwise, the next local configuration is an active process with the arguments of the selected method, a default store, and the body of the method as statement; additionally, a selection event is generated. -/
| ⟨σ, process.nil _⟩ := let e := θ.sched σ.id in option.elim e
    (λ_, ∅) (λd h, {⟨σ, process.schedule p σ d h⟩})
    -- TODO (event.selection d)
/- Otherwise, there is an active process. We look at the list of statements. If the list is empty, the process becomes inactive. -/
| ⟨σ, process.active ⟨e,τ,ℓ,[]⟩⟩ := {⟨σ, process.nil _⟩}
/- Otherwise, there is a current statement. If the current statement is an if statement, for which we evaluate the boolean pure expression. If it is true, we replace the current statement by those of the then-branch. Otherwise, we replace the current statement by those of the else-branch. -/
| ⟨σ, process.active π@⟨e,τ,ℓ,(stmt.ite p thenb elseb :: t)⟩⟩ :=
    match (eval σ π p).the.unbool with
    | tt := {⟨σ, process.active
        ⟨e,τ,ℓ,stmt.to_list thenb ++ t⟩⟩}
    | ff := {⟨σ, process.active
        ⟨e,τ,ℓ,stmt.to_list elseb ++ t⟩⟩}
    end
/- Otherwise, there is a while statement. We evaluate the boolean pure expression. If it is true, we prepend the body to all statements, before but including the current while statement. Otherwise, we discard the current statement. -/
| ⟨σ, process.active π@⟨e,τ,ℓ,S@(stmt.while p dob :: t)⟩⟩ :=
    match (eval σ π p).the.unbool with
    | tt := {⟨σ, process.active ⟨e,τ,ℓ,stmt.to_list dob ++ S⟩⟩}
    | ff := {⟨σ, process.active ⟨e,τ,ℓ,t⟩⟩}
    end
/- Otherwise, we consider the assignment statement. We evaluate the pure expression, and the result is taken to update the variable on the left-hand side: if it is a field then the object space field state is updated, otherwise it is a local and the store is updated. In both cases, the current statement is discarded. -/
| ⟨σ, process.active
      π@⟨e,τ,ℓ,(stmt.assign (svar.fvar f) p :: t)⟩⟩ :=
    {⟨σ.updatev f (eval σ π p).the, process.active ⟨e,τ,ℓ,t⟩⟩}
| ⟨σ, process.active
      π@⟨e,τ,ℓ,(stmt.assign (svar.lvar ⟨l⟩) p :: t)⟩⟩ :=
    {⟨σ, process.active ⟨e,τ,ℓ.update l (eval σ π p).the,t⟩⟩}
/- Otherwise, we have an async statement. We evaluate the argument list to a value list; the object pure expression is evaluated to an object value. If that value is null, no step is taken. Otherwise, we generate a method selection event with our object as caller and the appropriate call site, and discard the current statement. -/
| ⟨σ, process.active π@⟨e,τ,ℓ,(stmt.async c m G o τ' :: t)⟩⟩ :=
    (π.lookup σ o).elim_object
      (λo h, {⟨σ, process.active ⟨e,τ,ℓ,t⟩⟩})
      -- TODO (event.call σ.id ⟨o,m,eval σ π τ'⟩)
      (λ_, ∅)
/- Otherwise, we have an alloc statement. We evaluate the argument list to a value list. A fresh object identity is obtained from the global history, and stored in the variable. A call event to the constructor of the freshly obtained object is generated with an approriate call site, and the current statement is discarded. -/
| ⟨σ, process.active
      π@⟨e,τ,ℓ,(stmt.alloc c (svar.fvar f) τ' :: t)⟩⟩ :=
    {r : local_config α β C |
    ∃o : {o // c = objects.class_of α o}, θ.fresh o ∧
    let new := value.object o in
      r = ⟨σ.updatev f new, process.active ⟨e,τ,ℓ,t⟩⟩}
    -- TODO (event.call σ.id ⟨o,ctor c,eval σ π τ'⟩
| ⟨σ, process.active 
      π@⟨e,τ,ℓ,(stmt.alloc c (svar.lvar ⟨l⟩) τ' :: t)⟩⟩ :=
    {r : local_config α β C |
    ∃o : {o // c = objects.class_of α o}, θ.fresh o ∧
    let new := value.object o in
      r = ⟨σ, process.active ⟨e,τ,ℓ.update l new,t⟩⟩}
    -- TODO (event.call σ.id ⟨o,ctor c,eval σ π τ'⟩)
