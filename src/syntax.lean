-- (C) Copyright 2019, Hans-Dieter Hiep

import data.finmap

section syntax

/-
We have the following class of names.
Names have decidable equality.
Given a finite set of names,
there can always be given a fresh instance not in that set.
(with thanks to Johannes Hölzl)
-/
class fixed_names (α : Type) :=
(deceq: decidable_eq α)
class names (α : Type) extends fixed_names α :=
(fresh: finset α → α)
(fresh_is_new: ∀x : finset α, (fresh x) ∉ x)

-- Class names (Nc)
variables {Nc : Type} [HNc: fixed_names Nc]
-- Field names (Nf)
variables {Nf : Type} [HNf: fixed_names Nf]
-- Method names (Nm)
variables {Nm : Type} [HNm: fixed_names Nm]
-- Local variables (V)
variables {V : Type}  [HV: names V]

/-
A type in our object language is either:
a reference type (by class name),
a future of some type,
or a data type from the host language.
-/
inductive type : Type 1
| reference: Nc -> type
| future: type -> type
| data: Type -> type

structure vardecl : Type 1 :=
(ty : @type Nc) (var : V)

/-
A program signature consists of:
a finite map from class names to class declarations, and
a (declared) class name of the root object.

A class declaration consists of:
a finite map from field names to types, and
a finite map from method names to method declarations.

A method declaration consists of:
a return type and a list of typed formal parameters.
-/

structure mdecl : Type 1 :=
(rtype : @type Nc)
(fparam : list (@vardecl Nc V))

structure cdecl : Type 1 :=
(Mf : finmap Nf (λ_, @type Nc))
(Mm : finmap Nm (λ_, @mdecl Nc V))

structure signature : Type 1 :=
(Mc : finmap Nc (λ_, @cdecl Nc Nf Nm V))
(main : Nc)
(main_is_decl : main ∈ Mc)

end syntax
