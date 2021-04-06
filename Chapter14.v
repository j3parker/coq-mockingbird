From Mockingbird Require Export Chapter11.
Require Import Coq.Logic.ClassicalFacts.

Axiom day : Type.
Axiom sings : bird -> day -> Prop.

Notation "x , d !" := (sings x d) (at level 60).

Definition sing_on_same_days x y :=
  forall d, x,d! <-> y,d!.

Notation "x ~= y" := (sing_on_same_days x y) (at level 70).

Definition law_1 P := forall x y d,
  y,d! -> P;x;y,d!.

Definition law_2 P := forall x y d,
  ~x,d! -> P;x;y,d!.

Definition law_3 P := forall x y d,
  x,d! /\ P;x;y,d! -> y,d!.

Definition law_4 P := forall x, exists y,
  y ~= P;y;x.

Definition special :=
  exists P, law_1 P /\ law_2 P /\ law_3 P /\ law_4 P.

Definition all_birds_sing_on_all_days :=
  forall x d, x,d!.

Theorem ch14p1 :
  excluded_middle /\ special -> all_birds_sing_on_all_days.
Proof.
  intros [HEM [P [HL1 [HL2 [HL3 HL4]]]]] y d.
  specialize (HL4 y) as [x HL4].
  specialize (HL4 d).
  destruct (HEM (x,d!)) as [Hxd | Hnxd].
  - apply HL4 in Hxd as HPxyd.
    apply (HL3 x y d (conj Hxd HPxyd)).
  - apply (HL2 x y) in Hnxd as HPxyd.
    apply HL4 in HPxyd. contradiction.
Qed.

Definition special' :=
  exists P, law_1 P /\ law_2 P /\ law_3 P.

Theorem ch14p2 :
  excluded_middle /\ special' /\ cardinal_exists /\ lark_exists
    -> all_birds_sing_on_all_days.
Proof.
  intros [HEM [[P [HL1 [HL2 HL3]]] [[C HC] HLe]]].
  apply ch14p1. split. apply HEM.
  exists P. repeat split; try assumption.
  intros x.
  destruct (ch9p25 HLe) with (A := C;P;x) as [y].
  exists y.
  unfold is_fond_of in H. rewrite HC in H.
  rewrite H. easy.
Qed.

(* TODO: is there a good way to pose this without
         using the answer? *)

Theorem ch14p3 :
  excluded_middle /\ special'
  /\ (exists A, forall x y z, A;x;y;z = x;(z;z);y)
    -> all_birds_sing_on_all_days.
Proof.
  intros [HEM [[P [HL1 [HL2 HL3]]] [A HA]]].
  apply ch14p1. split. apply HEM.
  exists P. repeat split; try assumption.
  intros x. exists (A;P;x;(A;P;x)). intros d.
  rewrite <- HA. easy.
Qed.