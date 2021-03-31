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
  intros [[B HB] [[T HT] [M HM]]].
  exists (B;(T;M);B). intros x y.
  repeat (rewrite HB || rewrite HT || rewrite HM).
  reflexivity.
Qed.

Theorem ch12p3 :
  bluebird_exists /\ warbler_exists -> lark_exists.
Proof.
  intros [[B HB] [W HW]].
  exists (B;W;B). intros x y.
  rewrite HB. rewrite HW. rewrite HB.
  reflexivity.
Qed.

Theorem ch12p4 :
  mockingbird_exists /\ queer_exists -> lark_exists.
Proof.
  intros [[M HM] [Q HQ]].
  exists (Q;M). intros x y.
  rewrite HQ. rewrite HM.
  reflexivity.
Qed.

Definition converse_warbler Wp :=
  forall x y, Wp;x;y = y;x;x.
Definition converse_warbler_exists :=
  exists Wp, converse_warbler Wp.

Theorem ch12p5_the_bird_wp :
  btm_exists -> converse_warbler_exists.
Proof.
  intros [HBe [HTe [M HM]]].
  destruct (ch11p20_robins (conj HBe HTe)) as [R HR].
  destruct HBe as [B HB].
  destruct HTe as [T HT].
  exists (B;M;R). intros x y.
  rewrite HB. rewrite HM. repeat rewrite HR.
  reflexivity.
Qed.

Theorem ch12p6_the_warbler :
  bluebird_exists
  /\ robin_exists
  /\ cardinal_exists
  /\ mockingbird_exists -> warbler_exists.
Proof.
  intros [[B HB] [[R HR] [[C HC] [M HM]]]].
  (* C;W' works *)
  exists (C;(B;M;R)). intros x y.
  rewrite HC. rewrite HB. rewrite HM.
  repeat rewrite HR. reflexivity.
Qed.

Theorem ch12p7 :
  btm_exists -> warbler_exists.
Proof.
  intros [[B HB] [[T HT] [M HM]]].
  exists ((B;(T;(B;M;(B;B;T))));(B;B;T)). intros x y.
  repeat (rewrite HB || rewrite HT || rewrite HM).
  reflexivity.
Qed.

Theorem ch12p8_a_question :
  bluebird_exists /\ thrush_exists /\ warbler_exists
    -> mockingbird_exists.
Proof.
  intros [[B HB] [[T HT] [W HW]]].
  exists (W;T). intros x.
  rewrite HW. rewrite HT.
  reflexivity.
Qed.

Definition warbler_star Wx := forall x y z, Wx;x;y;z = x;y;z;z.
Definition warbler_star_exists := exists Wx, warbler_star Wx.

Definition warbler_star_star Wxx :=
  forall x y z w, Wxx;x;y;z;w = x;y;z;w;w.
Definition warbler_star_star_exists :=
  exists Wxx, warbler_star_star Wxx.

Theorem ch12p9_two_relatives_of_w :
  btm_exists -> warbler_star_exists /\ warbler_star_star_exists.
Proof.
  intros HBTMe.
  destruct (ch12p7 HBTMe) as [W HW].
  destruct HBTMe as [[B HB] [[T HT] [M HM]]].
  split.
  - exists (B;W). intros x y z.
    rewrite HB. rewrite HW.
    reflexivity.
  - exists (B;(B;W)). intros x y z w.
    repeat rewrite HB. rewrite HW.
    reflexivity.
Qed.

Definition hummingbird H := forall x y z, H;x;y;z = x;y;z;y.
Definition hummingbird_exists := exists H, hummingbird H.

Theorem ch12p10_warblers_and_hummingbirds :
  bluebird_exists /\ cardinal_exists /\ warbler_exists
    -> hummingbird_exists.
Proof.
  intros [[B HB] [[C HC] [W HW]]].
  exists (B;W;(B;C)). intros x y z.
  rewrite HB. rewrite HW. rewrite HB. rewrite HC.
  reflexivity.
Qed.

Theorem ch12p11_hummingbirds_and_warblers :
  hummingbird_exists /\ robin_exists 
    -> warbler_exists.
Proof.
  intros [[H HH] HRe].
  destruct (ch11p21_robins_and_cardinals HRe) as [C HC].
  destruct HRe as [R HR].
  exists (C;(H;R)). intros x y.
  rewrite HC. rewrite HH. rewrite HR.
  reflexivity.
Qed.

Definition starling S := forall x y z, S;x;y;z = x;z;(y;z).
Definition starling_exists := exists S, starling S.

Theorem ch12p12_starlings :
  btm_exists -> starling_exists.
Proof.
  intros HBTMe.
  destruct (ch12p7 HBTMe) as [W HW].
  destruct HBTMe as [HBe [HTe _]].
  destruct (ch11p47_goldfinches (conj HBe HTe)) as [G HG].
  destruct HBe as [B HB].
  exists (B;(B;W);G). intros x y z.
  repeat rewrite HB. rewrite HW. rewrite HG.
  reflexivity.
Qed.

Theorem ch12p13_hummingbirds_revisited :
  starling_exists /\ robin_exists
    -> hummingbird_exists.
Proof.
  intros [[S HS] HRe].
  destruct (ch11p21_robins_and_cardinals HRe) as [C HC].
  exists (S;(C;C)). intros x y z.
  rewrite HS. repeat rewrite HC.
  reflexivity.
Qed.

Theorem ch12p14 :
  starling_exists /\ robin_exists
    -> warbler_exists.
Proof.
  intros H'.
  destruct (ch12p13_hummingbirds_revisited H') as [H HH].
  apply ch12p11_hummingbirds_and_warblers. split. 
  - exists H. apply HH.
  - destruct H' as [_ HRe]. assumption.
Qed.

Theorem ch12p15 :
  thrush_exists /\ starling_exists -> warbler_exists.
Proof.
  intros [[T HT] [S HS]].
  exists (S;T). intros x y.
  rewrite HS. rewrite HT.
  reflexivity.
Qed.

Theorem ch12p16 :
  thrush_exists /\ starling_exists -> mockingbird_exists.
Proof.
  intros [[T HT] [S HS]].
  exists (S;T;T). intros x.
  rewrite HS. repeat rewrite HT.
  reflexivity.
Qed.

(* todo: exercises *)