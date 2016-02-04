Set Implicit Arguments.
Unset Strict Implicits.

Require Import Ssreflect.ssreflect Ssreflect.ssrbool.
Require Import Coq.Program.Wf Coq.Classes.SetoidClass Coq.Logic.FunctionalExtensionality.

Require Import taseq monad union.

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
  (* It is impossible to prove (arrs |> eff_pure == arrs) *)
  (* What axiom to be able to prove (arrs |> eff_pure == arrs) ? *)
End EqArrs.

Section EffMonad.

  Definition eff_pure {R} {A} (a : A) := Pure R a.
  Definition eff_bind {R} {A B} (e : Eff R A) (f : A -> Eff R B) :=
    match e with
    | Pure a => f a
    | Impure _ u q => Impure u (q |> f)
    end.

  Existing Instance arrs_setoid.

  Lemma enq_pure_pure :
    forall R A,
      SOne (Eff R) (@eff_pure R A) |> eff_pure == (SOne _ eff_pure).
  Proof.
    move=> R A a.
    by compute.
  Qed.

  Lemma enq_f_pure :
    forall R A (f : A -> Eff R A),
      SOne _ f |> eff_pure == SOne _ f.
  Proof.
    move=> R A f a.
    compute.
    case H : (f a); first done.
    congr (_ _).
    admit.                      (* impossible *)
  Qed.

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
        admit.                  (* impossible *)
    - admit.
  Qed.

  Lemma enq_r_to_l :
    forall R A B C D (arrs : Arrs R A B) (k : B -> Eff R C) (h : C -> Eff R D),
      arrs |> (fun a => eff_bind (k a) h) == arrs |> k |> h.
  Proof.
    move=> R A B C D; elim=> //=.
    - move=> X f k h a.
      case H : (f a)=> [ x | X' u s ].
      + compute; rewrite H.
        by case H' : (k x).
      + compute; rewrite H.
        congr (_ _).
        admit.                  (* impossible *)
    - admit.
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
