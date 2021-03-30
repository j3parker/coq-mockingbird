From Mockingbird Require Import Chapter9.

Definition bluebird B := forall x y z, B;x;y;z = x;(y;z).
Definition bluebird_exists := exists B, bluebird B.

Theorem ch11p1 :
  bluebird_exists -> composition_exists.
Proof.
  intros [B HB] x y.
  exists (B;x;y). intros z.
  rewrite HB. reflexivity.
Qed.

Theorem ch11p2_bluebirds_and_mockingbirds :
  bluebird_exists /\ mockingbird_exists
    -> forall x, exists F, x <3 F.
  (* Note: the question asks for an F in terms of M, x,
           and B. We are capturing the spirit of that
           because the premises only include those birds. *)
Proof.
  intros [[B HB] [M HM]] x. unfold is_fond_of.
  exists (M;(B;x;M)).
  rewrite <- HB. rewrite HM. reflexivity.
Qed.

Theorem ch11p3_egocentric :
  bluebird_exists /\ mockingbird_exists
    -> egocentric_exists.
Proof.
  intros [HBe HMe].
  apply (ch9p2_egocentric
    (conj (ch11p1 HBe) HMe)).
Qed.

Theorem ch11p4_hopelessly_egocentric :
  bluebird_exists /\ mockingbird_exists /\ kestrel_exists
    -> hopelessly_egocentric_exists.
Proof.
  intros [HBe [HMe [K HK]]].
  apply ch11p1 in HBe as HCe.
  destruct (ch9p1_the_significance_of_the_mockingbird (conj HCe HMe) K) as [F HKFF].
  exists F. intros x.
  assert (H: F; x = K; F; x). { rewrite HKFF. reflexivity. }
  rewrite H. rewrite HK. reflexivity.
Qed.

Definition dove D := forall x y z w, D;x;y;z;w = x;y;(z;w).
Definition dove_exists := exists D, dove D.

Definition ch11p5_doves :
  bluebird_exists -> dove_exists.
Proof.
  intros [B HB].
  exists (B;B). intros x y z w.
  repeat rewrite HB. reflexivity.
Qed.

Definition blackbird B1 :=
  forall x y z w, B1;x;y;z;w = x;(y;z;w).
Definition blackbird_exists := exists B1, blackbird B1.

Definition ch11p6_blackbirds :
  bluebird_exists -> blackbird_exists.
Proof.
  intros [B HB].
  exists (B;B;B). intros x y z w.
  repeat rewrite HB. reflexivity.
  (* alternative: D;B
  intros HBe.
  inversion HBe as [B HB].
  destruct (ch11p5_doves HBe) as [D HD].
  exists (D;B). intros x y z w.
  rewrite HD. rewrite HB. reflexivity. *)
Qed.

Definition eagle E :=
  forall x y z w v, E;x;y;z;w;v = x;y;(z;w;v).
Definition eagle_exists := exists E, eagle E.

Definition ch11p7_eagles :
  bluebird_exists -> eagle_exists.
Proof.
  intros [B HB].
  exists (B;(B;B;B)). intros x y z w v.
  repeat rewrite HB. reflexivity.
  (* alternative: B;B1
  intros HBe.
  inversion HBe as [B HB].
  destruct (ch11p6_blackbirds HBe) as [B1 HB1].
  exists (B;B1). intros x y z w v.
  rewrite HB. rewrite HB1. reflexivity. *)
Qed.

Definition bunting B2 :=
  forall x y z w v, B2;x;y;z;w;v = x;(y;z;w;v).
Definition bunting_exists := exists B2, bunting B2.

Definition ch11p8_buntings :
  bluebird_exists -> bunting_exists.
Proof.
  intros [B HB].
  exists (B;(B;B;B);B). intros x y z w v.
  repeat rewrite HB. reflexivity.
  (* alternative: E;B.
  intros HBe.
  inversion HBe as [B HB].
  destruct (ch11p7_eagles HBe) as [E HE].
  exists (E;B). intros x y z w v.
  rewrite HE. rewrite HB. reflexivity. *)
Qed.

Definition dickcissel D1 :=
  forall x y z w v, D1;x;y;z;w;v = x;y;z;(w;v).
Definition dickcissel_exists := exists D1, dickcissel D1.

Definition ch11p9_dickcissels :
  bluebird_exists -> dickcissel_exists.
Proof.
  intros [B HB].
  exists (B;B;B;B). intros x y z w v.
  repeat rewrite HB. reflexivity.
  (* alternative: B1;B.
  intros HBe.
  inversion HBe as [B HB].
  destruct (ch11p6_blackbirds HBe) as [B1 HB1].
  exists (B1;B). intros x y z w v.
  rewrite HB1. rewrite HB. reflexivity. *)
Qed.

Definition becard B3 :=
  forall x y z w, B3;x;y;z;w = x;(y;(z;w)).
Definition becard_exists := exists B3, becard B3.

Definition ch11p10_becards :
  bluebird_exists -> becard_exists.
Proof.
  intros [B HB].
  exists (B;B;B;B;B). intros x y z w.
  repeat rewrite HB. reflexivity.
Qed.

Definition dovekie D2 := 
  forall x y z w v, D2;x;y;z;w;v = x;(y;z);(w;v).
Definition dovekie_exists := exists D2, dovekie D2.

Theorem ch11p11_dovekies :
  bluebird_exists -> dovekie_exists.
Proof.
  intros [B HB].
  exists (B;B;B;B;B;B). intros x y z w v.
  repeat rewrite HB. reflexivity.
  (* alternative: B3;B.
  intros HBe.
  inversion HBe as [B HB].
  destruct (ch11p10_becards HBe) as [B3 HB3].
  exists (B3;B). intros x y z w v.
  rewrite HB3. rewrite HB. reflexivity. *)
Qed.

Definition bald_eagle E := forall x y1 y2 y3 z1 z2 z3,
  E;x;y1;y2;y3;z1;z2;z3 = x;(y1;y2;y3);(z1;z2;z3).
Definition bald_eagle_exists := exists E, bald_eagle E.

Theorem ch11p12_bald_eagles :
  bluebird_exists -> bald_eagle_exists.
Proof.
  intros [B HB].
  exists (B;(B;B;B);(B;(B;B;B))). intros x y1 y2 y3 z1 z2 z3.
  repeat rewrite HB. reflexivity.
  (* alternative: E;E
  intros HBe.
  inversion HBe as [B HB].
  destruct (ch11p7_eagles HBe) as [E HE].
  exists (E;E). intros x y1 y2 y3 z1 z2 z3.
  repeat rewrite HE. reflexivity. *) 
Qed.

Definition warbler W := forall x y, W;x;y = x;y;y.
Definition warbler_exists := exists W, warbler W.

Theorem ch11p13_warblers :
  warbler_exists /\ kestrel_exists -> mockingbird_exists.
Proof.
  intros [[W HW] [K HK]].
  exists (W;(W;K)). intros x.
  repeat rewrite HW. rewrite HK.
  reflexivity.
Qed.

Theorem ch11p14 :
  warbler_exists /\ identity_exists -> mockingbird_exists.
Proof.
  intros [[W HW] [I HI]].
  exists (W;I). intros x.
  rewrite HW. rewrite HI.
  reflexivity.
Qed.

Theorem ch11p15 :
  warbler_exists /\ kestrel_exists -> identity_exists.
Proof.
  intros [[W HW] [K HK]].
  exists (W;K). intros x.
  rewrite HW. rewrite HK.
  reflexivity.
Qed.

Definition cardinal C := forall x y z, C;x;y;z = x;z;y.
Definition cardinal_exists := exists C, cardinal C.

Theorem ch11p16_cardinals :
  cardinal_exists /\ kestrel_exists -> identity_exists.
Proof.
  intros [[C HC] [K HK]].
  exists (C;K;K). intros x.
  rewrite HC. repeat rewrite HK.
  reflexivity.
Qed.

Definition thrush T := forall x y, T;x;y = y;x.
Definition thrush_exists := exists T, thrush T.

Theorem ch11p17_thrushes :
  cardinal_exists /\ identity_exists -> thrush_exists.
Proof.
  intros [[C HC] [I HI]].
  exists (C;I). intros x y.
  rewrite HC. rewrite HI.
  reflexivity.
Qed.

Definition commutes x y := x;y = y;x.
Definition universal_commuter_exists :=
  exists C, forall x, commutes C x.

Theorem ch11p18_commuting_birds :
  thrush_exists /\ (forall A, exists F, A <3 F)
    -> universal_commuter_exists.
Proof.
  intros [[T HT] HFe].
  destruct (HFe T) as [F HTFF].
  exists (T;F). intros x.
  inversion HTFF. unfold commutes.
  rewrite H. rewrite HT. rewrite H.
  reflexivity.
Qed.

Theorem ch11p19 :
  bluebird_exists /\ thrush_exists /\ mockingbird_exists
    -> universal_commuter_exists.
Proof.
  intros [HBe [HTe HMe]].
  apply (ch11p18_commuting_birds (conj
    HTe
    (ch11p2_bluebirds_and_mockingbirds (conj HBe HMe))
  )).
Qed.

Definition robin R := forall x y z, R;x;y;z = y;z;x.
Definition robin_exists := exists R, robin R.

Theorem ch11p20_robins :
  bluebird_exists /\ thrush_exists -> robin_exists.
Proof.
  intros [[B HB] [T HT]].
  exists (B;B;T). intros x y z.
  repeat rewrite HB. rewrite HT.
  reflexivity.
Qed.

Theorem ch11p21_robins_and_cardinals :
  robin_exists -> cardinal_exists.
Proof.
  intros [R HR].
  exists (R;R;R). intros x y z.
  repeat rewrite HR. reflexivity.
Qed.

Lemma cardinal_from_bluebird_and_thrush :
  bluebird_exists /\ thrush_exists -> cardinal_exists.
Proof.
  intros H.
  apply ch11p21_robins_and_cardinals.
  apply ch11p20_robins.
  assumption.
Qed.

Theorem ch11p22_two_useful_laws_part1 :
  forall C R x, cardinal C /\ robin R
    -> C;x = R;x;R.
Proof.
  (* Needs functional extensionality as written?
     Is it fair to pose it differently? *)
Admitted.

Theorem ch11p22_two_useful_laws_part2 :
  forall C B T R x, cardinal C /\ bluebird B /\ robin R
    -> C;x = B;(T;x);R.
Proof.
  (* Needs functional extensionality as written?
     Is it fair to pose it differently? *)
Admitted.

Theorem ch11p23_a_question :
  cardinal_exists -> robin_exists.
Proof.
  intros [C HC].
  exists (C;C). intros x y z.
  repeat rewrite HC. reflexivity.
Qed.

Definition finch F := forall x y z, F;x;y;z = z;y;x.
Definition finch_exists := exists F, finch F.

Theorem ch11p24_finches :
  bluebird_exists /\ thrush_exists -> finch_exists.
Proof.
  intros H.
  inversion H as [[B HB] [T HT]].
  destruct (ch11p20_robins H) as [R HR].
  destruct ch11p21_robins_and_cardinals as [C HC].
    exists R. apply HR.
  exists (B;C;R). intros x y z.
  rewrite HB. rewrite HC. rewrite HR.
  reflexivity.
Qed.

Theorem ch11p25 :
  thrush_exists /\ eagle_exists -> finch_exists.
Proof.
  intros [[T HT] [E HE]].
  exists (E;T;T;E;T). intros x y z.
  repeat (rewrite HT || rewrite HE).
  reflexivity.
Qed.

(* todo: express p26 *)

Definition vireo V := forall x y z, V;x;y;z = z;x;y.
Definition vireo_exists := exists V, vireo V.

Theorem ch11p27_vireos :
  bluebird_exists /\ thrush_exists -> vireo_exists.
Proof.
  intros H.
  inversion H as [[B HB] [T HT]].
  destruct (ch11p24_finches H) as [F HF].
  Search cardinal_exists.
  destruct (ch11p21_robins_and_cardinals (ch11p20_robins H)) as [C HC].
  exists (C;F). intros x y z.
  rewrite HC. rewrite HF. reflexivity.
Qed.

(* todo: express p28 *)

Theorem ch11p29_a_question :
  cardinal_exists /\ vireo_exists -> finch_exists.
Proof.
  intros [[C HC] [V HV]].
  exists (C;V). intros x y z.
  rewrite HC. rewrite HV. reflexivity.
Qed.

Theorem ch11p30_a_curiosity :
  robin_exists /\ kestrel_exists -> identity_exists.
Proof.
  intros [[R HR] [K HK]].
  exists (R; K; K). intros x.
  rewrite HR. repeat rewrite HK.
  reflexivity.
Qed.

Definition cardinal_1r C :=
  forall x y z w, C;x;y;z;w = x;y;w;z.
Definition cardinal_1r_exists := exists C, cardinal_1r C.

Theorem ch11p31_the_bird_c1r :
  bluebird_exists /\ cardinal_exists -> cardinal_1r_exists.
Proof.
  intros [[B HB] [C HC]].
  exists (B;C). intros x y z w.
  rewrite HB. rewrite HC.
  reflexivity.
Qed.

Definition robin_1r R :=
  forall x y z w, R;x;y;z;w = x;z;w;y.
Definition robin_1r_exists := exists R, robin_1r R.

Theorem ch11p32_the_bird_r1r :
  bluebird_exists /\ cardinal_exists -> robin_1r_exists.
Proof.
  intros H.
  destruct (ch11p31_the_bird_c1r H) as [C1r HC1r].
  destruct H as [[B HB] [C HC]].
  exists (C1r;C1r). intros x y z w.
  repeat rewrite HC1r. reflexivity.
Qed.

Definition finch_1r F :=
  forall x y z w, F;x;y;z;w = x;w;z;y.
Definition finch_1r_exists := exists F, finch_1r F.

Theorem ch11p33_the_bird_f1r :
  bluebird_exists /\ cardinal_exists -> finch_1r_exists.
Proof.
  intros H.
  destruct (ch11p31_the_bird_c1r H) as [C1r HC1r].
  destruct H as [[B HB] [C HC]].
  (* used vireo-once-removed here *)
  exists (C1r;(B;C1r;C)). intros x y z w.
  repeat (rewrite HC1r || rewrite HB || rewrite HC).
  reflexivity.
Qed.

Definition vireo_1r V :=
  forall x y z w, V;x;y;z;w = x;w;y;z.
Definition vireo_1r_exists := exists V, vireo_1r V.

Theorem ch11p34_the_bird_v1r :
  bluebird_exists /\ cardinal_exists -> vireo_1r_exists.
Proof.
  intros H.
  destruct (ch11p31_the_bird_c1r H) as [C1r HC1r].
  destruct H as [[B HB] [C HC]].
  exists (B;C1r;C). intros x y z w.
  rewrite HB. rewrite HC1r. rewrite HC.
  reflexivity.
Qed.

Definition cardinal_2r C :=
  forall x y z1 z2 z3, C;x;y;z1;z2;z3 = x;y;z1;z3;z2.
Definition cardinal_2r_exists := exists C, cardinal_2r C.

Definition robin_2r R :=
  forall x y z1 z2 z3, R;x;y;z1;z2;z3 = x;y;z2;z3;z1.
Definition robin_2r_exists := exists R, robin_2r R.

Definition finch_2r F :=
  forall x y z1 z2 z3, F;x;y;z1;z2;z3 = x;y;z3;z2;z1.
Definition finch_2r_exists := exists F, finch_2r F.

Definition vireo_2r V :=
  forall x y z1 z2 z3, V;x;y;z1;z2;z3 = x;y;z3;z1;z2.
Definition vireo_2r_exists := exists V, vireo_2r V.

Theorem ch11p35_twice_removed :
  bluebird_exists /\ cardinal_exists
    -> cardinal_2r_exists
    /\ robin_2r_exists
    /\ finch_2r_exists
    /\ vireo_2r_exists.
Proof.
  intros H.
  inversion H as [HBe HCe].
  inversion HBe as [B HB].
  inversion HCe as [C HC].
  repeat split.
  - destruct (ch11p31_the_bird_c1r H) as [C1r HC1r].
    exists (B;C1r). intros x y z1 z2 z3.
    rewrite HB. rewrite HC1r. reflexivity.
  - destruct (ch11p32_the_bird_r1r H) as [R1r HR1r].
    exists (B;R1r). intros x y z1 z2 z3.
    rewrite HB. rewrite HR1r. reflexivity.
  - destruct (ch11p33_the_bird_f1r H) as [F1r HF1r].
    exists (B;F1r). intros x y z1 z2 z3.
    rewrite HB. rewrite HF1r. reflexivity.
  - destruct (ch11p34_the_bird_v1r H) as [V1r HV1r].
    exists (B;V1r). intros x y z1 z2 z3.
    rewrite HB. rewrite HV1r. reflexivity.
Qed.

Theorem ch11p36_vireos_revisted :
  cardinal_1r_exists /\ thrush_exists -> vireo_exists.
Proof.
  intros [[C1r HC1r] [T HT]].
  exists (C1r;T). intros x y z.
  rewrite HC1r. rewrite HT. reflexivity.
Qed.

Definition queer Q := forall x y z, Q;x;y;z = y;(x;z).
Definition queer_exists := exists Q, queer Q.

Theorem ch11p37_queer_birds :
  bluebird_exists /\ thrush_exists -> queer_exists.
Proof.
  intros H.
  destruct (cardinal_from_bluebird_and_thrush H) as [C HC].
  destruct H as [[B HB] _].
  exists (C;B). intros x y z.
  rewrite HC. rewrite HB. reflexivity.
Qed.

Definition quixotic Q1 := forall x y z, Q1;x;y;z = x;(z;y).
Definition quixotic_exists := exists Q1, quixotic Q1.

Theorem ch11p38_quixotic_birds :
  bluebird_exists /\ thrush_exists -> quixotic_exists.
Proof.
  intros H.
  destruct (cardinal_from_bluebird_and_thrush H) as [C HC].
  inversion H as [HBe [T HT]].
  destruct (ch11p6_blackbirds HBe) as [B1 HB1].
  exists (C;B1;T). intros x y z.
  rewrite HC. rewrite HB1. rewrite HT.
  reflexivity.
Qed.

Definition quizzical Q2 := forall x y z, Q2;x;y;z = y;(z;x).
Definition quizzical_exists := exists Q2, quizzical Q2.

Theorem ch11p39_quizzical_birds :
  bluebird_exists /\ thrush_exists -> quizzical_exists.
Proof.
  intros H.
  destruct (cardinal_from_bluebird_and_thrush H) as [C HC].
  inversion H as [HBe [T HT]].
  inversion HBe as [B HB].
  destruct (ch11p32_the_bird_r1r (conj HBe (ex_intro cardinal C HC))) as [R1r HR1r].
  exists (R1r;B). intros x y z.
  rewrite HR1r. rewrite HB.
  reflexivity.
Qed.

Theorem ch11p40_a_problem :
  cardinal_exists -> quixotic_exists <-> quizzical_exists.
Proof.
  intros [C HC]. split.
  - intros [Q1 HQ1].
    exists (C;Q1). intros x y z.
    rewrite HC. rewrite HQ1.
    reflexivity.
  - intros [Q2 HQ2].
    exists (C;Q2). intros x y z.
    rewrite HC. rewrite HQ2.
    reflexivity.
Qed.

Definition quirky Q3 := forall x y z, Q3;x;y;z = z;(x;y).
Definition quirky_exists := exists Q3, quirky Q3.

Theorem ch11p41_quirky_birds :
  bluebird_exists /\ thrush_exists -> quirky_exists.
Proof.
  intros [[B HB] [T HT]].
  exists (B;T). intros x y z.
  rewrite HB. rewrite HT.
  reflexivity.
Qed.

Definition quacky Q4 := forall x y z, Q4;x;y;z = z;(y;x).
Definition quacky_exists := exists Q4, quacky Q4.

Theorem ch11p42_quacky_birds :
  bluebird_exists /\ thrush_exists -> quacky_exists.
Proof.
  intros [HBe [T HT]].
  destruct (ch11p6_blackbirds HBe) as [B1 HB1].
  destruct HBe as [B HB].
  exists (B1;T;T). intros x y z.
  rewrite HB1. repeat rewrite HT.
  reflexivity.
Qed.

Theorem ch11p43_an_old_proverb :
  cardinal_exists -> quirky_exists <-> quacky_exists.
Proof.
  intros [C HC]. split.
  - intros [Q3 HQ3].
    exists (C;Q3). intros x y z.
    rewrite HC. rewrite HQ3.
    reflexivity.
  - intros [Q4 HQ4].
    exists (C;Q4). intros x y z.
    rewrite HC. rewrite HQ4.
    reflexivity.
Qed.

Theorem ch11p44_a_question :
  quixotic_exists /\ thrush_exists -> quacky_exists.
Proof.
  intros [[Q1 HQ1] [T HT]].
  exists (Q1;T). intros x y z.
  rewrite HQ1. rewrite HT.
  reflexivity.
Qed.

Theorem ch11p45_an_interesting_fact_about_the_queer_bird_Q :
  queer_exists /\ thrush_exists -> bluebird_exists.
Proof.
  intros [[Q HQ] [T HT]].
  exists (Q;T;(Q;Q)). intros x y z.
  repeat (rewrite HQ || rewrite HT).
  reflexivity.
Qed.

Theorem ch11p46 :
  queer_exists /\ thrush_exists -> cardinal_exists.
Proof.
  intros [[Q HQ] [T HT]].
  exists (Q;Q;(Q;T)). intros x y z.
  repeat (rewrite HQ || rewrite HT).
  reflexivity.
Qed.

Definition goldfinch G
  := forall x y z w, G;x;y;z;w = x;w;(y;z).
Definition goldfinch_exists := exists G, goldfinch G.

Theorem ch11p47_goldfinches :
  bluebird_exists /\ thrush_exists -> goldfinch_exists.
Proof.
  intros H.
  destruct (cardinal_from_bluebird_and_thrush H) as [C HC].
  destruct H as [[B HB] _].
  exists (B;B;C). intros x y z w.
  repeat rewrite HB. rewrite HC.
  reflexivity.
Qed.
