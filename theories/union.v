Set Implicit Arguments.
Unset Strict Implicits.

Require Import Coq.Lists.List.

Inductive Union' (X : Type) : list (Type -> Type) -> Type :=
| Inl : forall F R, F X -> Union' X (cons F R)
| Inr : forall F R, Union' X R -> Union' X (cons F R).

Definition Union (R : list (Type -> Type)) := fun X => Union' X R.
