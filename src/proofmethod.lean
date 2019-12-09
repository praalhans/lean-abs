
import semantics

variables {α β : Type} [objects α β]

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
