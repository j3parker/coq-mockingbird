From Mockingbird Require Export Chapter14.

Definition law_1 e := forall x y d,
  e;x;y,d! -> y,d!.

Definition law_2 e := forall x y d,
  ~(x,d! /\ e;x;y,d!).

Definition law_3 e := forall x y d,
  ~x,d! /\ y,d! -> e;x;y,d!.

Definition law_4 e := forall x, exists y, forall d,
  y,d! <-> e;x;y,d!.

Definition special e :=
  law_1 e /\ law_2 e /\ law_3 e /\ law_4 e.

Theorem ch16 :
  exists e, special e -> forall x d, ~x,d!.
Proof.
Admitted.