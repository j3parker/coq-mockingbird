From Mockingbird Require Export Chapter10.
From Mockingbird Require Export Chapter12.

Theorem ch13p1 :
  mockingbird_exists /\ bluebird_exists /\ robin_exists
    -> sage_exists.
Proof.
  intros [[M HM] [[B HB] [R HR]]].
Admitted.

Theorem ch13p2 :
  bluebird_exists /\ cardinal_exists /\ mockingbird_exists
    -> sage_exists.
Proof.
  intros [[M HM] [[B HB] [R HR]]].
Admitted.

Theorem ch13p3 :
  mockingbird_exists /\ bluebird_exists /\ lark_exists
    -> sage_exists.
Proof.
  intros [[M HM] [[B HB] [L HL]]].
Admitted.

Theorem ch13p4 :
  mockingbird_exists /\ bluebird_exists /\ warbler_exists
    -> sage_exists.
Proof.
  intros [[M HM] [[B HB] [W HW]]].
Admitted.

Theorem ch13p5 :
  bluebird_exists /\ cardinal_exists /\ warbler_exists
    -> sage_exists.
Proof.
  intros [[B HB] [[C HC] [W HW]]].
Admitted.

Theorem ch13p6 :
  queer_exists /\ lark_exists /\ warbler_exists
    -> sage_exists.
Proof.
  intros [[Q HQ] [[L HL] [W HW]]].
Admitted.

(* ch13p7 isn't a new problem *)

Theorem ch13p8_queer_birds_and_mockingbirds :
  queer_exists /\ mockingbird_exists -> sage_exists.
Proof.
  intros [[Q HQ] [M HM]].
Admitted.

Theorem ch13p9_starlings_and_larks :
  starling_exists /\ lark_exists -> sage_exists.
Proof.
  intros [[S HS] [L HL]].
Admitted.