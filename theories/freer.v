Set Implicit Arguments.
Unset Strict Implicits.

Require Import Ssreflect.ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import monad union.

Inductive Freer (F : Type -> Type) (A : Type) : Type :=
| Pure : A -> Freer F A
| Impure : forall (X : Type), F X -> (X -> Freer F A) -> Freer F A.

Definition freer_pure {F} {A} (a : A) := Pure F a.
Fixpoint freer_bind {F} {A B} (ffa : Freer F A) (f : A -> Freer F B) :=
  match ffa with
  | Pure a => f a
  | Impure _ fx k => Impure fx (fun x => freer_bind (k x) f)
  end.

Program Instance freer_monad (F : Type -> Type) : Monad (Freer F) := {
  pure := (@freer_pure F);
  bind := (@freer_bind F)
}.
Next Obligation.
  elim: ma=> //=.
  move=> X f k IH; congr (_ _).
    by apply: functional_extensionality.
Qed.
Next Obligation.
  elim: ma=> //=.
  move=> X fx f IH; congr (_ _).
    by apply: functional_extensionality.
Qed.

Definition UnefficientEff (R : list (Type -> Type)) := Freer (Union R).
