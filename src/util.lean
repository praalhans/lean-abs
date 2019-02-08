-- (C) Copyright 2019, Hans-Dieter Hiep

import data.finmap data.bool data.vector data.list data.stream

open stream nat option

universe u
variable {α : Type u}

/-
List membership with concrete witness (position)
-/
inductive list_at: α → list α → Type u
| head (x : α) (xs : list α): list_at x (x :: xs)
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

/-
A generated stream is a stream of optional elements.
Each generated stream has these properties:
The head is not none.
Given an occurence of none, all later elements are none.
-/
structure gstream (α : Type) : Type :=
(carrier : stream (option α))
(head : carrier 0 ≠ none)
(definite : ∀n, carrier n = none → ∀m ≥ n, carrier m = none)

/-
A generated stream with an occurrence of none
has a least occurence of none, and
the element before is called the last.
-/
def gstream.last {α : Type} (x : gstream α) :
Π n : ℕ, x.carrier n = none → ℕ
| 0 H := false.rec ℕ (x.head H)
| (succ m) H := if G : (x.carrier m = none)
    then (gstream.last m G)
    else m

lemma dite.is_false {c : Prop} [h : decidable c]
{α : Sort u} {t : c → α} {e : ¬c → α} (H : ¬c) :
dite c t e = e H :=
begin
    tactic.unfreeze_local_instances, cases h,
    constructor, exfalso, apply H, assumption
end

lemma dite.is_true {c : Prop} [h : decidable c]
{α : Sort u} {t : c → α} {e : ¬c → α} (H : c) :
dite c t e = t H :=
begin
    tactic.unfreeze_local_instances, cases h,
    exfalso, apply h, assumption, constructor
end

def gstream.concat {α : Type} (l : gstream α) (r : gstream α) : gstream α :=
⟨(λn, if H : l.carrier n = none
    then r.carrier (n - (gstream.last l n H))
    else l.carrier n),
begin
    have G : l.carrier 0 ≠ none, apply l.head,
    rewrite dite.is_false, assumption, assumption
end,
begin
    sorry
end⟩
