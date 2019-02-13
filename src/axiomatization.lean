
import semantics

open list

variables {α β : Type} [objects α β]

/- We consider the conditions required for reachable global histories. -/

/- A global history is a sequence of events, restricted to those in which for each object, the subsequence of selections to is a prefix of the subsequence of calls. -/
def valid_history_1 (θ : global_history α β) : Prop :=
  ∀ o : β, is_prefix (θ?o) (θ!o).

@[reducible]
def pending (α β : Type) [objects α β] :=
  finsupp β (queue (callsite α β))

def pending.add (p : pending α β) (o : β) (c : callsite α β) :
  pending α β := p.update o ((p o).add c)

inductive valid_history_2 (α β : Type) [objects α β] :
    list (event α β) → pending α β → Prop
| empty: valid_history_2 [] 0
| call (l : list (event α β)) (p : pending α β)
    (o : β) (c : callsite α β):
  valid_history_2 (l ++ [event.call o c]) (p.add o c)
-- TODO: add matching receive
