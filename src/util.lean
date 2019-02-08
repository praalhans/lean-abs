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
