From Mockingbird Require Export Chapter10.
From Mockingbird Require Export Chapter14.
Require Import Coq.Logic.Decidable.

Definition special a := forall x d,
  a;x,d! <-> x;x,d!.

Definition complementary_singer_exists :=
  forall x, exists x', forall y d,
    x';y,d! <-> ~x;y,d!.

Theorem ch15p1 :
  ~(exists a, special a /\ complementary_singer_exists).
Proof.
Admitted.

Definition special' N := forall x d,
  N;x,d! <-> ~x,d!.

Theorem ch15p2 :
  ~(exists N, special' N /\ sage_exists).
Proof.
Admitted.

Definition special'' A := forall x y d,
  A;x;y,d! <-> ~(x,d! \/ y,d!).

Theorem ch15p3 :
  decidable (exists A, special'' A /\ sage_exists).
Proof.
Admitted.