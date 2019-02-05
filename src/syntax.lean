-- (C) Copyright 2019, Hans-Dieter Hiep

-- TODO fix mathlib version (finmap)

/-
A type in our object language is either a reference type to
some class name, a future of some type, or a data type from
the host language.
-/

-- TODO we encode reference types by natural number;
-- we actually want to refer to an element of some name set.
inductive type : Type 1
| reference: nat -> type
| future: type -> type
| data: Type -> type

/-
A program signature consists of a finite map from class names
to class declarations. A class declaration consists of a
finite map from field names to types, and from method names
to method declarations. A method declaration consists of a return
type and a list of typed formal parameters.
-/
