Set Implicit Arguments.
Unset Strict Implicits.

Require Import Ssreflect.ssreflect.
Require Import MathClasses.interfaces.monads MathClasses.interfaces.canonical_names.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import union.

Inductive Freer (F : Type -> Type) (A : Type) : Type :=
| Pure : A -> Freer F A
| Impure : forall (X : Type), F X -> (X -> Freer F A) -> Freer F A.

Instance freer_return {F} : MonadReturn (Freer F) := fun a => @Pure F a.
Instance freer_bind {F} : MonadBind (Freer F) :=
  fix freer_bind {A B} f ffa :=
    match ffa with
    | Pure a => f a
    | Impure _ fx k => Impure fx (fun x => freer_bind f (k x))
    end.

Program Instance freer_equiv {F} : forall A, Equiv A -> Equiv (Freer F A).
Next Obligation.
  apply: eq.
Qed.

Program Instance freer_monad (F : Type -> Type) : Monad (Freer F).
Next Obligation.
  rewrite/Proper/respectful.
  move=> x y equiv.
  setoid_rewrite equiv.


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
