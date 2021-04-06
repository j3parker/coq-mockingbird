From Mockingbird Require Export Chapter10.
From Mockingbird Require Export Chapter14.
Require Import Coq.Logic.Decidable.
Require Import Coq.Logic.ClassicalFacts.

Definition special a := forall x d, a;x,d! <-> x;x,d!.

Definition complementary_singer_exists :=
  forall x, exists x', forall y d,
    x';y,d! <-> ~x;y,d!.

(* Although not mentioned in the books, some of the exercises
   implicitly assume there is at least one day. *)
Axiom today : day.

Theorem ch15p1 :
  ~(exists a, special a /\ complementary_singer_exists).
Proof.
  intros [a [HS HCe]].
  destruct (HCe a) as [a' Ha'].
  specialize (Ha' a' today).
  specialize (HS a' today).
  intuition.
Qed.

Definition special' N := forall x d,
  N;x,d! <-> ~x,d!.

Theorem ch15p2 :
  ~(exists N, special' N /\ sage_exists).
Proof.
  intros [N [HSp [S HSage]]].
  specialize (HSp (S;N) today).
  rewrite HSage in HSp.
  intuition.
Qed.

Definition special'' A := forall x y d,
  A;x;y,d! <-> ~(x,d! \/ y,d!).

Theorem ch15p3 : excluded_middle ->
  decidable (exists A, special'' A /\ sage_exists).
Proof.
  intros HEM. right. intros [A [HSp [S HSage]]].
Admitted.