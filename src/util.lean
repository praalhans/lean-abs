-- (C) Copyright 2019, Hans-Dieter Hiep

import data.finmap data.bool data.vector data.list data.multiset

open multiset nat option

universe u
variable {α : Type u}

/- Indices of a list -/
inductive pointer: list α → Type u
| here (x : α) (xs : list α): pointer (x :: xs)
| tail {xs : list α} (y : α): pointer xs → pointer (y :: xs)

/- List membership with concrete witness (position) -/
inductive list_at: α → list α → Type u
| here (x : α) (xs : list α): list_at x (x :: xs)
| tail {x : α} {l : list α} (y : α): list_at x l → list_at x (y :: l)

lemma list_at_mem {x : α} {l : list α} : list_at x l → x ∈ l :=
begin
    intro H,
    induction l,
    cases H,
    cases H,
    constructor, refl,
    have: x ∈ l_tl,
        apply l_ih, assumption,
    right, assumption
end

/- A FIFO queue is a list of elements. Adding an element appends it to the back. Removing an element takes it from the front. -/
@[derive decidable_eq]
structure queue (α : Type u) := (l : list α)

@[reducible]
def queue.add (q : queue α) (x : α) : queue α := ⟨q.l ++ [x]⟩
@[reducible]
def queue.empty : queue α → bool
| ⟨[]⟩ := tt
| ⟨(x :: l)⟩ := ff
def queue.full : queue α → Prop := λq, q ≠ ⟨[]⟩
@[reducible]
def queue.remove : Π q : queue α, queue.full q → α × queue α
| ⟨[]⟩ H := begin exfalso, apply H, simp end
| ⟨(x :: l)⟩ _ := ⟨x, ⟨l⟩⟩
@[reducible]
def queue.first (q : queue α) (H : queue.full q) : α :=
  (queue.remove q H).fst
@[reducible]
def queue.unshift (q : queue α) (H : queue.full q) : queue α :=
  (queue.remove q H).snd
@[reducible]
def queue.poll : queue α → option (α × queue α)
| ⟨[]⟩ := none
| ⟨(x :: l)⟩ := some ⟨x, ⟨l⟩⟩
instance queue.has_zero : has_zero (queue α) := ⟨⟨[]⟩⟩

/- A multiset can be seen as a stack: each element has a counter. Pushing an element increases the associated counter. Clearly, this is best seen when converting a multiset to a function with finite support. -/
def push: multiset α → α → multiset α := λm x, cons x m
