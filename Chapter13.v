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
  intros [[M HM] [HBe HWe]].
  destruct (ch12p3 (conj HBe HWe)) as [L HL].
  destruct HBe as [B HB].
  exists (B;M;L). intros x. unfold is_fond_of.
  rewrite HB. rewrite HM. rewrite <- HL.
  reflexivity.
Qed.

Theorem ch13p5 :
  bluebird_exists /\ cardinal_exists /\ warbler_exists
    -> sage_exists.
Proof.
  intros [HBe [[C HC] HWe]].
  destruct (ch12p3 (conj HBe HWe)) as [L HL].
  destruct HBe as [B HB].
  destruct HWe as [W HW].
  exists (W;(C;(B;B;L);L)). intros x. unfold is_fond_of.
  rewrite HW. rewrite HC. repeat rewrite HB.
  rewrite <- HL. reflexivity.
Qed.

Theorem ch13p6 :
  queer_exists /\ lark_exists /\ warbler_exists
    -> sage_exists.
Proof.
  intros [[Q HQ] [[L HL] [W HW]]].
  exists (W;(Q;L;(Q;L))). intros x. unfold is_fond_of.
  rewrite HW. repeat rewrite HQ. rewrite <- HL.
  reflexivity.
Qed.

(* ch13p7 isn't a new problem *)

Theorem ch13p8_queer_birds_and_mockingbirds :
  queer_exists /\ mockingbird_exists -> sage_exists.
Proof.
  intros [[Q HQ] [M HM]].
  exists (Q;(Q;M);M). intros x.
  rewrite HQ. unfold is_fond_of.
  rewrite <- HQ. rewrite <- HM.
  reflexivity.
Qed.

Theorem ch13p9_starlings_and_larks :
  starling_exists /\ lark_exists -> sage_exists.
Proof.
  intros [[S HS] [L HL]].
  exists (S;L;L). intros x. unfold is_fond_of.
  rewrite  HS. rewrite <- HL.
  reflexivity.
Qed.

Theorem ch13p10_currys_sage_bird :
  bluebird_exists /\ warbler_exists /\ starling_exists
    -> sage_exists.
Proof.
  intros [HBe [HWe HSe]].
  (* S;(B;W;B);(B;W;B) -> W;S;(B;W;B) *)
  pose (conj HBe HWe) as HLe. apply ch12p3 in HLe.
  apply (ch13p9_starlings_and_larks (conj HSe HLe)).
Qed.

Definition turing U := forall x y, U;x;y = y;(x;x;y).
Definition turing_exists := exists U, turing U.

Theorem ch13p11_finding_a_turing_bird :
  btm_exists -> turing_exists.
Proof.
  intros H.
  destruct (ch12p7 H) as [W HW].
  destruct H as [[B HB] [[T HT] [M HM]]].
  exists (B;W;(B;(B;T); M)). intros x y.
  repeat (rewrite HB || rewrite HW).
  rewrite HT. rewrite HM. reflexivity.
Qed.

Theorem ch13p12_turing_birds_and_sage_birds :
  turing_exists -> sage_exists.
Proof.
  intros [U HU].
  exists (U;U). intros x. unfold is_fond_of.
  rewrite <- HU. reflexivity.
Qed.

Definition owl O := forall x y, O;x;y = y;(x;y).
Definition owl_exists := exists O, owl O.

Theorem ch13p13_owls :
  queer_exists /\ warbler_exists -> owl_exists.
Proof.
  intros [[Q HQ] [W HW]].
  exists (Q;Q;W). intros x y.
  repeat (rewrite HQ || rewrite HW).
  reflexivity.
Qed.

Theorem ch13p14 :
  owl_exists /\ lark_exists -> turing_exists.
Proof.
  intros [[O HO] [L HL]].
  exists (L;O). intros x y.
  rewrite HL. rewrite HO.
  reflexivity.
Qed.

Theorem ch13p15 :
  owl_exists /\ identity_exists -> mockingbird_exists.
Proof.
  intros [[O HO] [I HI]].
  exists (O;I). intros x.
  rewrite HO. rewrite HI.
  reflexivity.
Qed.

Theorem ch13p16 :
  starling_exists /\ identity_exists -> owl_exists.
Proof.
  intros [[S HS] [I HI]].
  exists (S;I). intros x y.
  rewrite HS. rewrite HI.
  reflexivity.
Qed.

Theorem ch13p17_a_preliminary_problem :
  forall x y, x <3 y -> x <3 (x;y).
Proof.
  intros x y H. unfold is_fond_of in *.
  rewrite H. assumption.
Qed.

Theorem ch13p18 O S :
  owl O /\ sage S -> sage (O;S).
Proof.
  intros [HO HS] x. unfold is_fond_of.
  rewrite HO. repeat rewrite HS.
  reflexivity.
Qed.

Theorem ch13p19 O S :
  owl O /\ sage S -> sage (S;O).
Proof.
  intros [HO HS] x. unfold is_fond_of.
  rewrite <- HO. rewrite HS.
  reflexivity.
Qed.

Theorem ch13p20 O A :
  owl O /\ O <3 A -> sage A.
Proof.
  intros [HO HOFA] x. unfold is_fond_of.
  rewrite <- HO. rewrite HOFA.
  reflexivity.
Qed.

Definition choosy A := forall F, A <3 F -> sage F.

Theorem ch13p21 S A :
  sage S /\ choosy A -> sage (S;A).
Proof.
  intros [HS HCA].
  apply HCA. apply HS.
Qed.

Definition similar A B := forall x, A;x = B;x.
Notation "A ~= B" := (similar A B) (at level 50).

Theorem ch13p22_similarity O S :
  owl O /\ sage S -> O;S ~= S.
Proof.
  intros [HO HS] x.
  rewrite HO. apply HS.
Qed.

Definition extensional_forest :=
  forall A B, A ~= B -> A = B.

Theorem ch13p23 O :
  owl O /\ extensional_forest
    -> forall S, sage S -> O <3 S.
Proof.
  intros [HO HExt] S HS. unfold is_fond_of.
  apply HExt. intros x.
  apply (ch13p22_similarity O S (conj HO HS)).
Qed.