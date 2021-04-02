From Mockingbird Require Export Chapter10.
From Mockingbird Require Export Chapter14.
Require Import Coq.Logic.Decidable.

Definition special a := forall x d,
  sings (a;x) d <-> sings (x;x) d.

Definition complementary_singer_exists :=
  forall x, exists x', forall y d,
    sings (x';y) d <-> ~(sings (x;y) d).

Theorem ch15p1 :
  exists a, special a /\ complementary_singer_exists
    -> False.
Proof.
Admitted.

Definition special' N := forall x d,
  sings (N;x) d <-> ~(sings x d).

Theorem ch15p2 :
  exists N, special' N /\ sage_exists -> False.
Proof.
Admitted.

Definition special'' A := forall x y d,
  sings (A;x;y) d <-> ~(sings x d \/ sings y d).

Theorem ch15p3 :
  decidable (exists A, special'' A /\ sage_exists).
Proof.
Admitted.