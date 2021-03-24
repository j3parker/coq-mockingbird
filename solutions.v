Axiom bird : Type.
Axiom call : bird -> bird -> bird.

Notation "A ; B" := (call A B) (at level 50).

Definition composes (C A B : bird) : Prop :=
  forall (x : bird), C;x = A;(B;x).

Definition mockingbird M := forall (x : bird), M;x = x;x.
Definition mockingbird_exists := exists M, mockingbird M.

Definition composition_exists :=
  forall A B, exists C, composes C A B.

Definition is_fond_of A B := A;B = B.

Notation "A <3 B" := (is_fond_of A B) (at level 50).

Definition every_bird_is_fond_of_some_bird :=
  forall A, exists F, A <3 F.

Lemma ch9p1_the_significance_of_the_mockingbird :
  composition_exists /\ mockingbird_exists
    -> every_bird_is_fond_of_some_bird.
Proof.
  intros [HCe [M HM]] A.
  destruct (HCe A M) as [C HC].
  exists (C;C).
  assert (H: C;C = A;(M;C)). apply HC.
  destruct (HM C). easy.
Qed.

Definition egocentric E := E <3 E.
Definition egocentric_exists := exists E, egocentric E.

Theorem ch9p1_egocentric :
  composition_exists /\ mockingbird_exists
  -> egocentric_exists.
Proof.
  intros HF.
  inversion HF as [HCe [M HM]].
  destruct (ch9p1_the_significance_of_the_mockingbird HF M) as [E HE].
  exists E.
  pose (H := HM E). inversion H as [HE'].
  rewrite HE in HE'. easy.
Qed.

Definition agrees A B x := A;x = B;x.
Definition agreeable A := forall B, exists x, agrees A B x.

Theorem ch9p3_story_of_the_agreeable_bird :
  composition_exists /\ (exists A, agreeable A)
  -> every_bird_is_fond_of_some_bird.
Proof.
  intros [HCe [B HBA]] A.
  destruct (HCe A B) as [C HC].
  destruct (HBA C) as [F HA].
  unfold agrees in HA. rewrite HC in HA.
  exists (B;F). easy.
Qed.

Theorem ch9p4_a_question_on_agreeable_birds :
  composition_exists -> forall C A B,
    composes C A B /\ agreeable C -> agreeable A.
Proof.
  intros HCe C A B [HC HCA] D.
  destruct (HCe D B) as [DB HDB].
  destruct (HCA DB) as [x HCDBx].
  unfold agrees in *.
  rewrite HDB in HCDBx. rewrite HC in HCDBx.
  exists (B;x). assumption.
Qed.

Theorem ch9p5_an_exercise_in_composition :
  composition_exists ->
   forall A B C,
   exists D,
   forall x,
     D;x = A;(B;(C;x)).
Proof.
  intros HCe A B C.
  destruct (HCe B C) as [E HEC].
  destruct (HCe A E) as [D HDC].
  exists D. intros x.
  rewrite <- (HEC x).
  rewrite <- (HDC x).
  reflexivity.
Qed.

Definition compatible A B : Prop :=
  exists x y, A;x = y /\ B;y = x.

Theorem ch9p6_compatible_birds :
  composition_exists /\ mockingbird_exists
  -> forall A B, compatible A B.
Proof.
  intros HF A B.
  inversion HF as [HCe [M HM]].
  destruct (HCe A B) as [C HC].
  destruct (ch9p1_the_significance_of_the_mockingbird HF C) as [F HCFF].
  unfold is_fond_of in HCFF.
  rewrite HC in HCFF.
  exists (B;F). exists F.
  split; easy.
Qed.

Definition happy A := compatible A A.

Theorem ch9p7_happy_birds :
  forall A F, A <3 F -> happy A.
Proof.
  intros A F HAF.
  repeat exists F.
  split; assumption.
Qed.

Definition normal A := exists F, A <3 F.

Theorem ch9p8_normal_birds :
  composition_exists /\ (exists A, happy A)
    -> exists N, normal N.
Proof.
  intros [HCe [A HAH]].
  destruct (HCe A A) as [C HC].
  destruct HAH as [x [y [H H']]].
  rewrite <- H' in H.
  exists C. exists y.
  rewrite <- HC in H. easy.
Qed.

Definition hopelessly_egocentric H := forall x, H;x = H.
Definition hopelessly_egocentric_exists :=
  exists H, hopelessly_egocentric H.

Definition fixated A B := forall x, A;x = B.

Definition kestrel K := forall x y, (K;x);y = x.
Definition kestrel_exists := exists K, kestrel K.

Theorem ch9p9_hopelessly_egocentric :
  composition_exists /\ mockingbird_exists /\ kestrel_exists
  -> hopelessly_egocentric_exists.
Proof.
  intros [HCe [HMe [K HK]]]. inversion HMe as [M HM].
  destruct (ch9p1_the_significance_of_the_mockingbird (conj HCe HMe) K) as [F HKFF].
  exists (K;F). unfold hopelessly_egocentric. intros x.
  rewrite HK. easy.
Qed.

Theorem ch9p10_fixation :
  forall x y, fixated x y -> x <3 y.
Proof.
  intros x y Hxfy.
  apply Hxfy.
Qed.

Theorem ch9p11_a_fact_about_kestrels :
  forall K, kestrel K /\ egocentric K
    -> hopelessly_egocentric K.
Proof.
  intros K [HK HEK] x.
  unfold egocentric in HEK. unfold is_fond_of in HEK.
  rewrite <- HEK. rewrite HK. easy.
Qed.

Theorem ch9p12_another_fact_about_kestrels :
  forall K x, kestrel K /\ egocentric (K;x) -> K <3 x.
Proof.
  intros K x [HK HE].
  unfold egocentric in HE. unfold is_fond_of in HE.
  rewrite HK in HE. easy.
Qed.

Theorem ch9p13_a_simple_exercise :
  forall A, hopelessly_egocentric A
    -> forall x y, A;x = A;y.
Proof.
  intros A HHE x y.
  repeat rewrite HHE. reflexivity.
Qed.

Theorem ch9p14_another_exercise :
  forall A, hopelessly_egocentric A
    -> forall x y, (A;x);y = A.
Proof.
  intros A HHE x y.
  repeat rewrite HHE. reflexivity.
Qed.

Theorem ch9p15_hopeless_egocentricity_is_contagious :
  forall A, hopelessly_egocentric A
    -> forall x, hopelessly_egocentric (A;x).
Proof.
  intros A HHE x.
  rewrite HHE. assumption.
Qed.

Theorem ch9p16_another_fact_about_kestrels :
  forall K, kestrel K
    -> forall x y, K;x = K;y -> x = y.
Proof.
  intros K HK x y HKeq.
  destruct (HK x y).
  rewrite HKeq.
  apply HK.
Qed.

Definition kestrel_cancellation :=
  ch9p16_another_fact_about_kestrels.

Theorem ch9p17_a_fact_about_fixation :
  forall A x y, fixated A x /\ fixated A y -> x = y.
Proof.
  intros A x y [HFx HFy].
  destruct (HFx x). apply HFy.
Qed.

Theorem ch9p18_another_fact_about_kestrels :
  forall K x, kestrel K /\ K <3 (K;x) -> K <3 x.
Proof.
  intros K x [HK H].
  apply (kestrel_cancellation K HK) in H.
  assumption.
Qed.

Theorem ch9p19_a_riddle :
  forall K, kestrel K /\ hopelessly_egocentric K
    -> forall A, A = K.
Proof.
  intros K [HK HKHE] A.
  destruct (HKHE A). destruct (HKHE A).
  easy. 
Qed.

Definition identity I := forall x, I;x = x.
Definition identity_exists := exists I, identity I.

Theorem ch9p20 :
  forall I, identity I /\ agreeable I -> forall A, normal A.
Proof.
  intros I [HI HIA] A.
  destruct (HIA A) as [F].
  inversion H as [H'].
  rewrite HI in H'.
  exists F. easy.
Qed.

Theorem ch9p21 :
  forall I, identity I /\ every_bird_is_fond_of_some_bird
    -> agreeable I.
Proof.
  intros I [HI HF] A.
  destruct (HF A) as [F HAF].
  exists F. unfold agrees.
  rewrite HI. easy.
Qed.

Theorem ch9p22 :
  forall I, identity I /\ (forall A B, compatible A B)
    -> (forall A, agreeable A \/ agreeable I).
Proof.
  intros I [HI HCompat] A. right.
  intros B.
  destruct (HCompat I B).
  destruct H. destruct H as [H H'].
  rewrite HI in H. subst.
  exists x0. unfold agrees. rewrite HI. easy.
Qed.

Theorem ch9p23_why :
  forall I, identity I /\ hopelessly_egocentric I
    -> forall A, I = A.
Proof.
  intros I [HI HEI] A.
  unfold hopelessly_egocentric in HEI.
  destruct (HEI A).
  apply HI.
Qed.

Definition lark L := forall x y, L;x;y = x;(y;y).
Definition lark_exists := exists L, lark L.

Theorem ch9p24 :
  lark_exists /\ identity_exists -> mockingbird_exists.
Proof.
  intros [[L HL] [I HI]].
  pose (M := L;I). exists M.
  intros x. unfold M. rewrite HL. rewrite HI.
  reflexivity.
Qed.

Theorem ch9p25 :
  lark_exists -> (forall A, normal A).
Proof.
  intros [L HL] A.
  exists (L;A;(L;A)). 
  unfold is_fond_of. rewrite <- HL. reflexivity.
Qed.

Theorem ch9p26_another_riddle :
  forall L, lark L /\ hopelessly_egocentric L
    -> forall A, A <3 L.
Proof.
  intros L [HL HHEL] A.
  destruct (HHEL L).
  destruct (HHEL L).
  unfold is_fond_of. rewrite <- HL.
  repeat rewrite HHEL. reflexivity.
Qed.

Theorem ch9p27 :
  forall L K, lark L /\ kestrel K
    -> L <> K -> ~(L <3 K).
Proof.
  intros L K [HL HK] Hne HLFK.
  destruct Hne. unfold is_fond_of in HLFK.
Admitted. 

Theorem ch9p28 :
  forall L K, lark L /\ kestrel K /\ K <3 L
    -> forall A, A <3 L.
Proof.
  intros L K [HL [HK HKFL]] A.
  assert (HLHE: hopelessly_egocentric L). {
    intros x. rewrite <- HKFL. rewrite HK. easy.
  }
  apply (ch9p26_another_riddle L (conj HL HLHE)).
Qed.

Theorem ch9p29 :
  lark_exists -> exists E, egocentric E.
Proof.
  intros HLe. inversion HLe as [L HL].
  destruct (ch9p25 HLe L) as [F HLFF].
  Print egocentric.
Admitted.

Theorem ch10_is_there_a_sage_bird :
  forall M, mockingbird M /\ composition_exists
    /\ (exists A, forall x, composes (A;x) x M)
      -> exists S, forall x, x <3 (S;x).
Proof.
  intros M [HM [HCe [A HA]]].
  destruct (HCe M A) as [S HS]. exists S. intros x.
  unfold is_fond_of.
  assert (H: S;x = x;(S;x)). {
    rewrite HS.
    rewrite <- HA.
    rewrite <- HM.
    reflexivity.
  }
  rewrite <- H. reflexivity.
Qed.

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
  intros [[B HB] [M HM]].
Admitted.

Theorem ch11p4_hopelessly_egocentric :
  bluebird_exists /\ mockingbird_exists /\ kestrel_exists
    -> hopelessly_egocentric_exists.
Proof.
  intros [[B HB] [[M HM] [K HK]]].
Admitted.

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

Theorem ch11p18_commuting_birds :
  thrush_exists /\ (forall A, exists F, A <3 F)
    -> (exists A, forall x, commutes A x).
Proof.
  intros [[T HT] HFe].
  destruct (HFe T) as [F HTFF].
  exists (T;F). intros x.
  inversion HTFF. unfold commutes.
  rewrite H. rewrite HT. rewrite H.
  reflexivity.
Qed.