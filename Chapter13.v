From Mockingbird Require Export Chapter10.
From Mockingbird Require Export Chapter12.

Lemma bm_fondness B M x :
  bluebird B -> mockingbird M -> x <3 (M;(B;x;M)).
Proof.
  intros HB HM. unfold is_fond_of.
  rewrite <- HB.
  rewrite <- HM.
  reflexivity.
Qed.
 
Theorem ch13p1 :
  mockingbird_exists /\ bluebird_exists /\ robin_exists
    -> sage_exists.
Proof.
  intros [[M HM] [[B HB] [R HR]]].
  exists (B;M;(R;M;B)). intros x.
  rewrite HB. rewrite HR.
  apply (bm_fondness B M); assumption.
Qed.

Theorem ch13p2 :
  bluebird_exists /\ cardinal_exists /\ mockingbird_exists
    -> sage_exists.
Proof.
  intros [[B HB] [[C HC] [M HM]]].
  exists (B;M;(C;B;M)). intros x.
  rewrite HB. rewrite HC.
  apply (bm_fondness B M); assumption.
Qed.

Theorem ch13p3 :
  mockingbird_exists /\ bluebird_exists /\ lark_exists
    -> sage_exists.
Proof.
  intros [[M HM] [[B HB] [L HL]]].
  exists (B;M;L). intros x.
  rewrite HB. rewrite HM.
  unfold is_fond_of.
  rewrite <- HL. reflexivity.
Qed.

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

Theorem ch13p10_currys_sage_bird :
  bluebird_exists /\ warbler_exists /\ starling_exists
    -> sage_exists.
Proof.
Admitted.

Definition turing U := forall x y, U;x;y = y;(x;x;y).
Definition turing_exists := exists U, turing U.

Theorem ch13p11_finding_a_turing_bird :
  btm_exists -> turing_exists.
Proof.
Admitted.

Theorem ch13p12_turing_birds_and_sage_birds :
  turing_exists -> sage_exists.
Proof.
Admitted.

Definition owl O := forall x y, O;x;y = y;(x;y).
Definition owl_exists := exists O, owl O.

Theorem ch13p13_owls :
  queer_exists /\ warbler_exists -> owl_exists.
Proof.
Admitted.

Theorem ch13p14 :
  owl_exists /\ lark_exists -> turing_exists.
Proof.
Admitted.

Theorem ch13p15 :
  owl_exists /\ identity_exists -> mockingbird_exists.
Proof.
Admitted.

Theorem ch13p16 :
  starling_exists /\ identity_exists -> owl_exists.
Proof.
Admitted.

Theorem ch13p17_a_preliminary_problem :
  forall x y, x <3 y -> x <3 (x;y).
Proof.
  intros x y H. unfold is_fond_of in *.
  rewrite H. assumption.
Qed.

Theorem ch13p18 O S :
  owl O /\ sage S -> sage (O;S).
Proof.
Admitted.

Theorem ch13p19 O S :
  owl O /\ sage S -> sage (S;O).
Proof.
Admitted.

Theorem ch13p20 O A :
  owl O /\ O <3 A -> sage A.
Proof.
Admitted.

Definition choosy A := forall F, A <3 F -> sage F.

Theorem ch13p21 S A :
  sage S /\ choosy A -> sage (S;A).
Proof.
Admitted.

Definition similar A B := forall x, A;x = B;x.
Notation "A ~= B" := (similar A B) (at level 50).

Theorem ch13p22_similarity O S :
  owl O /\ sage S -> O;S ~= S.
Proof.
Admitted.

Definition extensional_forest :=
  forall A B, A ~= B -> A = B.

Theorem ch13p23 O :
  owl O /\ extensional_forest
    -> forall S, sage S -> O <3 S.
Proof.
Admitted.