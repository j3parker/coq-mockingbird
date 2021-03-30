From Mockingbird Require Export Chapter11.

Definition double_mockingbird M2 :=
  forall x y, M2;x;y = x;y;(x;y).
Definition double_mockingbird_exists :=
  exists M2, double_mockingbird M2.

Theorem ch12p1_the_bird_m2 :
  bluebird_exists /\ mockingbird_exists
    -> double_mockingbird_exists.
Proof.
  intros [[B HB] [M HM]].
  exists (B;M). intros x y.
  rewrite HB. rewrite HM.
  reflexivity.
Qed.

Definition btm_exists :=
  bluebird_exists /\ thrush_exists /\ mockingbird_exists.

Theorem ch12p2_larks :
  btm_exists -> lark_exists.
Proof.
Admitted.

Theorem ch12p3 :
  bluebird_exists /\ warbler_exists -> lark_exists.
Proof.
Admitted.

Theorem ch12p4 :
  mockingbird_exists /\ queer_exists -> lark_exists.
Proof.
Admitted.

Definition converse_warbler Wp :=
  forall x y, Wp;x;y = y;x;x.
Definition converse_warbler_exists :=
  exists Wp, converse_warbler Wp.

Theorem ch12p5_the_bird_wp :
  btm_exists -> converse_warbler_exists.
Proof.
Admitted.

Theorem ch12p6_the_warbler :
  bluebird_exists
  /\ robin_exists
  /\ cardinal_exists
  /\ mockingbird_exists -> warbler_exists.
Proof.
Admitted.

Theorem ch12p7 :
  btm_exists -> warbler_exists.
Proof.
Admitted.

Theorem ch12p8_a_question :
  bluebird_exists /\ thrush_exists /\ warbler_exists
    -> mockingbird_exists.
Proof.
Admitted.

Definition warbler_star Wx := forall x y z, Wx;x;y;z = x;y;z;z.
Definition warbler_star_exists := exists Wx, warbler_star Wx.

Definition warbler_star_star Wxx :=
  forall x y z w, Wxx;x;y;z;w = x;y;z;w;w.
Definition warbler_star_star_exists :=
  exists Wxx, warbler_star_star Wxx.

Theorem ch12p9_two_relatives_of_w :
  btm_exists -> warbler_star_exists /\ warbler_star_star_exists.
Proof.
Admitted.

Definition hummingbird H := forall x y z, H;x;y;z = x;y;z;y.
Definition hummingbird_exists := exists H, hummingbird H.

Theorem ch12p10_warblers_and_hummingbirds :
  bluebird_exists /\ cardinal_exists /\ warbler_exists
    -> hummingbird_exists.
Proof.
Admitted.

Theorem ch12p11_hummingbirds_and_warblers :
  hummingbird_exists /\ (
    (bluebird_exists /\ cardinal_exists)
    \/ cardinal_exists
    \/ robin_exists 
  ) -> warbler_exists.
Proof.
  intros H.
Admitted.

Definition starling S := forall x y z, S;x;y;z = x;z;(y;z).
Definition starling_exists := exists S, starling S.

Theorem ch12p12_starlings :
  btm_exists -> starling_exists.
Proof.
Admitted.

Theorem ch12p13_hummingbirds_revisited :
  starling_exists /\ (cardinal_exists \/ robin_exists)
    -> hummingbird_exists.
Proof.
Admitted.

Theorem ch12p14 :
  starling_exists /\ (robin_exists \/ cardinal_exists)
    -> warbler_exists.
Proof.
Admitted.

Theorem ch12p15 :
  thrush_exists /\ starling_exists -> warbler_exists.
Proof.
Admitted.

Theorem ch12p16 :
  thrush_exists /\ starling_exists -> mockingbird_exists.
Proof.
Admitted.

(* todo: exercises *)