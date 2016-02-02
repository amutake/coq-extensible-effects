Set Implicit Arguments.
Unset Strict Implicits.

Require Import Ssreflect.ssreflect Ssreflect.ssrbool.
Require Import Coq.Program.Wf Coq.Classes.SetoidClass Coq.Logic.FunctionalExtensionality.

Require Import taseq monad union.

(**
 * We want to define like below, but it cannot compile
Inductive arrows (R : list (Type -> Type)) : Type -> Type -> Type :=
| Leaf : forall {A B}, (A -> eff R B) -> arrows R A B
| Node : forall {A B C}, arrows R A B -> arrows R B C -> arrows R A C
with eff (R : list (Type -> Type)) (A : Type) : Type :=
| Pure : A -> eff R A
| Impure : forall {X}, union R X -> arrows R X A -> eff R A.
(* => parameters should be syntactically the same for each inductive type *)
 * ok, switch to the below. this can compile.
Inductive arrows (R : list (Type -> Type)) : Type -> Type -> Type :=
| Leaf : forall {A B}, (A -> eff R B) -> arrows R A B
| Node : forall {A B C}, arrows R A B -> arrows R B C -> arrows R A C
with eff (R : list (Type -> Type)) : Type -> Type :=
| Pure : forall A, A -> eff R A
| Impure : forall {A X}, union R X -> arrows R X A -> eff R A.
 * but there is a defect in this `eff` definition
Definition foo {R} {A B} (e : eff R A) (f : A -> eff R B) :=
  match e with
  | Pure _ a => f a             (* => `a` does not have type A *)
  | ...
 *
 * To avoid mutual inductive definition, we define arrows parameterized by F
 *)

Inductive Eff (R : list (Type -> Type)) (A : Type) : Type :=
| Pure : A -> Eff R A
| Impure : forall {X}, Union R X -> SnocNel (Eff R) X A -> Eff R A.

Definition Arrs (R : list (Type -> Type)) (A B : Type) := SnocNel (Eff R) A B.

Program Fixpoint tapp {R} {A B} (q : Arrs R A B) (a : A) {measure (tsize q)} : Eff R B :=
  match tviewl q with
  | TOne k => k a
  | TCons _ k t =>
    match k a with
    | Pure a' => tapp t a'
    | Impure _ u q' => Impure u (q' |><| t)
    end
  end.
Next Obligation.
  by rewrite [tsize q]tviewl_preserve_size -Heq_anonymous /=.
Defined.

Section EqArrs.

  Variable R : list (Type -> Type).
  Variable A B : Type.

  Definition eqarrs (f g : Arrs R A B) :=
    forall a : A, tapp f a = tapp g a.

  Lemma arefl (f : Arrs R A B) : eqarrs f f.
  Proof. by done. Qed.
  Lemma asym (f g : Arrs R A B) : eqarrs f g -> eqarrs g f.
  Proof. by rewrite/eqarrs. Qed.
  Lemma atrans (f g h : Arrs R A B) : eqarrs f g -> eqarrs g h -> eqarrs f h.
  Proof.
      by rewrite/eqarrs=> H H' a; move: (H a) (H' a)=> -> ->.
  Qed.

  Program Instance arrs_setoid : Setoid (Arrs R A B) := {
    equiv := eqarrs
  }.
  Next Obligation.
    split.
    - by apply: arefl.
    - by apply: asym.
    - by apply: atrans.
  Qed.

  Axiom arrs_ext : forall f g, f == g -> f = g.
  (* It is impossible to prove (arrs |> eff_pure == arrs) because
   * if tapp arrs a = Impure u q Impure _ (q *)
  (* What axiom to prove (arrs |> eff_pure == arrs) ? *)
End EqArrs.

Section EffMonad.

  Definition eff_pure {R} {A} (a : A) := Pure R a.
  Definition eff_bind {R} {A B} (e : Eff R A) (f : A -> Eff R B) :=
    match e with
    | Pure a => f a
    | Impure _ u q => Impure u (q |> f)
    end.

  Existing Instance arrs_setoid.
  (* apply (enq arrs f) = f (apply arrs) *)
  Lemma enq_pure :
    forall R A B (arrs : Arrs R A B),
      arrs |> eff_pure == arrs.
  Proof.
    move=> R A B; elim=> //=.
    - move=> X k.
      rewrite/eqarrs=> a.
      case H : (k a).
      + compute; by rewrite H.
      + compute.
        rewrite H.
        congr (_ _).
        apply arrs_ext.
        admit.
    - admit.
  Qed.

  Lemma enq_r_to_l :
    forall R A B C D (arrs : Arrs R A B) (k : B -> Eff R C) (h : C -> Eff R D),
      arrs |> (fun a => eff_bind (k a) h) == arrs |> k |> h.
  Proof.
    admit.
  Qed.

  Program Instance eff_is_monad (R : list (Type -> Type)) : Monad (Eff R) := {
    pure A := eff_pure;
    bind A B := eff_bind
  }.
  Next Obligation.
    elim: ma=> //=.
    move=> X u arrs; congr (_ _).
    apply: arrs_ext.
    by apply: enq_pure.
  Qed.
  Next Obligation.
    elim: ma=> //=.
    move=> X u arrs; congr (_ _).
    apply: arrs_ext.
    by apply: enq_r_to_l.
  Qed.
End EffMonad.
