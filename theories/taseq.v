Set Implicit Arguments.
Unset Strict Implicits.

Require Import Ssreflect.ssreflect.

(* SnocNel is the non empty version of SnocList (haskell's type-aligned package) *)
(* It is better to use FastQueue, but I use SnocNel for simplicity *)
Inductive SnocNel (M : Type -> Type) (A : Type) : Type -> Type :=
| SOne : forall {B}, (A -> M B) -> SnocNel M A B
| Snoc : forall {B X}, SnocNel M A X -> (X -> M B) -> SnocNel M A B.

Fixpoint tsize {M} {A B} (q : SnocNel M A B) : nat :=
  match q with
  | SOne _ _ => 1
  | Snoc _ _ q' _ => S (tsize q')
  end.

Definition tsingleton {M} {A B} (f : A -> M B) := SOne _ f.
Definition tsnoc {M} {A B C} (q : SnocNel M A B) (f : B -> M C) := Snoc q f.
Fixpoint tappend {M} {A B C} (ql : SnocNel M A B) (qr : SnocNel M B C) :=
  match qr with
  | SOne _ f => Snoc ql f
  | Snoc _ _ qr' f => Snoc (tappend ql qr') f
  end.
Notation "q |> f" := (tsnoc q f) (at level 10).
Notation "ql |><| qr" := (tappend ql qr) (at level 10).

Inductive ViewL (M : Type -> Type) (A B : Type) :=
| TOne : (A -> M B) -> ViewL M A B
| TCons : forall X, (A -> M X) -> SnocNel M X B -> ViewL M A B.

Fixpoint tviewl {M} {A B} (q : SnocNel M A B) : ViewL M A B :=
  match q with
  | SOne _ f => TOne _ _ f
  | Snoc _ _ q' f =>
    match tviewl q' with
    | TOne g => TCons g (SOne _ f)
    | TCons _ g s => TCons g (Snoc s f)
    end
  end.

Fixpoint vsize {M} {A B} (t : ViewL M A B) :=
  match t with
  | TOne _ => 1
  | TCons _ _ s => S (tsize s)
  end.

Lemma tviewl_preserve_size :
  forall M A B (q : SnocNel M A B),
    tsize q = vsize (tviewl q).
Proof.
  move=> M A B; elim=> // /=.
  move=> B' X s IH f.
  by case H : (tviewl s)=> /=; rewrite IH H /=.
Qed.
