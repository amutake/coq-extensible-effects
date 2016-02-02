Set Implicit Arguments.
Unset Strict Implicits.

Require Import Ssreflect.ssreflect.

Reserved Notation "ma >>= f" (at level 40, left associativity).
Class Monad (M : Type -> Type) : Prop := {
  pure : forall {A}, A -> M A;
  bind : forall {A B}, M A -> (A -> M B) -> M B
    where "ma >>= f" := (bind ma f);
  monad_law_pure_l : forall {A B} (a : A) (k : A -> M B), pure a >>= k = k a;
  monad_law_pure_r : forall {A} (ma : M A), ma >>= pure = ma;
  monad_law_assoc : forall {A B C} (ma : M A) (k : A -> M B) (h : B -> M C),
      ma >>= (fun a => k a >>= h) = ma >>= k >>= h
}.

Module Examples.
  Instance option_monad : Monad option := {
    pure := Some;
    bind A B oa f := match oa with
                     | None => None
                     | Some a => f a
                     end
  }.
  Proof.
    - move=> //.
    - move=> ?; case=> //.
    - move=> ? ? ?; case=> //.
  Qed.
End Examples.
