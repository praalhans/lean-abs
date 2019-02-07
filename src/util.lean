-- (C) Copyright 2019, Hans-Dieter Hiep

universe u
variable {α : Type u}

inductive list_at: α → list α → Type u
| head (x : α) (xs : list α): list_at x (x :: xs)
| tail (x y : α) (l : list α): list_at x l → list_at x (y :: l)

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
