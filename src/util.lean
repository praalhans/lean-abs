/- Copyright 2019 (c) Hans-Dieter Hiep. All rights reserved. Released under MIT license as described in the file LICENSE. -/

import data.finmap data.bool data.vector data.list data.multiset
import data.finsupp

open multiset nat option finset list

universes u v
variables {α : Type u} {β : Type v}

/- Indices of a list -/
@[derive decidable_eq]
inductive pointer: list α → Type u
| here (x : α) (xs : list α): pointer (x :: xs)
| tail {xs : list α} (y : α): pointer xs → pointer (y :: xs)

/- List membership with concrete witness (position) -/
@[derive decidable_eq]
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

/- A function with finite support can be updated. This either adds a new value, or overwrites the value previoulsy mapped. -/
namespace finsupp
variables [decidable_eq α] [decidable_eq β] [has_zero β]

def update (f : α →₀ β) (a : α) (b : β) : α →₀ β :=
  ⟨if b = 0 then f.support.erase a else f.support ∪ {a},
   (λa', if a = a' then b else f a'), λa',
    begin
      by_cases H : (a = a'); by_cases G : (b = 0); simp [G,H],
      { split, {intro, cases a_1, assumption}, {intro,
          have : ¬a' = a, intro, apply H,
            apply eq.symm, assumption, 
          exact ⟨this, a_1⟩ } },
      { split, {intro, cases a_1, exfalso,
          apply H, apply eq.symm, assumption, assumption},
        { intro, right, assumption } }
    end⟩

@[simp]
theorem update.to_fun (f : α →₀ β) (a : α) (b : β) :
  (update f a b).to_fun = (λa', if a = a' then b else f a') := rfl

@[simp]
theorem update.app_new_eq (f : α →₀ β) (a : α) (b : β) :
  (update f a b) a = b :=
begin
  simp [coe_fn], unfold has_coe_to_fun.coe, simp
end

theorem update.app_old_eq (f : α →₀ β) (a : α) (b : β)
    (c : α) (H : a ≠ c) :
  (update f a b) c = f c :=
begin
  simp [coe_fn], unfold has_coe_to_fun.coe, simp [H, coe_fn],
  unfold has_coe_to_fun.coe
end

end finsupp

/- Elimination and matching with equality (thanks to Rob Lewis) -/
def option.elim {α : Type u} {β : Sort v} (t : option α)
    (f : t = none → β) (g : Π(a : α), t = some a → β) : β :=
  match t, rfl : (∀ b, t = b → β) with
  | none, h := f h
  | (some a), h := g a h
  end

/- Lift list of options -/
lemma head_lift_nil {α : Type u} {a : α} :
  head (lift (@nil α)) ≠ some a :=
begin
  intro,
  simp [lift, has_lift.lift, default, inhabited.default] at a_1,
  assumption
end
lemma tail_lift_some {α : Type u} {hd a : α} {tl : list α} :
  head (lift (list.cons hd tl)) = some a → hd = a :=
begin
  intro,
  simp [lift, has_lift.lift, coe] at a_1,
  simp [lift_t, has_lift_t.lift, coe_t, has_coe_t.coe] at a_1,
  assumption
end
