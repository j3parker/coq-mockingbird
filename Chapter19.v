From Mockingbird Require Export Chapter12.

Definition jaybird J := forall x y z w,
  J;x;y;z;w = x;y;(x;w;z).
Definition jaybird_exists := exists J, jaybird J.

Theorem ch19p1_derivation_of_J :
  bluebird_exists /\ cardinal_exists /\ warbler_exists
    -> jaybird_exists.
Proof.
Admitted.

Theorem ch19p2_derivation_of_Q1 :
  jaybird_exists /\ identity_exists -> quixotic_exists.
Proof.
Admitted.

Theorem ch19p3_derivation_of_the_thrush :
  identity_exists /\ quixotic_exists -> thrush_exists.
Proof.
Admitted.

Theorem ch19p4_derivation_of_the_robin :
  jaybird_exists /\ thrush_exists -> robin_exists.
Proof.
Admitted.

Theorem ch19p5_derivation_of_the_bluebird :
  Prop. (* TODO: decide how to pose. *)
Proof.
Admitted.

Definition jaybird1 J1 := forall x y z w,
  J1;x;y;z;w = y;x;(w;x;z).
Definition jaybird1_exists := exists J1, jaybird1 J1.

Theorem ch19p6_the_bird_J1 :
  jaybird_exists /\ bluebird_exists /\ thrush_exists
    -> jaybird1_exists.
Proof.
Admitted.

Theorem ch19p7_the_mockingbird :
  cardinal_exists /\ thrush_exists /\ jaybird1_exists
    -> mockingbird_exists.
Proof.
Admitted.

