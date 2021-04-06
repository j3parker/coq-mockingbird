From Mockingbird Require Export Chapter11.

Axiom day : Type.
Axiom sings : bird -> day -> Prop.

Notation "x , d !" := (sings x d) (at level 60).

Definition sings_on_all_days x :=
  forall d, x,d!.

Notation "x !!" := (sings_on_all_days x) (at level 60).

Definition sing_on_same_days x y :=
  forall d, x,d! <-> y,d!.

Notation "x ~= y" := (sing_on_same_days x y) (at level 70).

(* Excluded middle restricted to the act of singing *)
Definition singing_em := forall x d, x,d! \/ ~x,d!.

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

Theorem ch14p1 :
  singing_em /\ special -> forall x, x!!.
Proof.
  intros [HEM [P [HL1 [HL2 [HL3 HL4]]]]] y d.
  specialize (HL4 y) as [x HL4].
  specialize (HL4 d).
  destruct (HEM x d) as [Hxd | Hnxd].
  - apply HL4 in Hxd as HPxyd.
    apply (HL3 x y d (conj Hxd HPxyd)).
  - apply (HL2 x y) in Hnxd as HPxyd.
    apply HL4 in HPxyd. contradiction.
Qed.

Definition first_three_laws P :=
  law_1 P /\ law_2 P /\ law_3 P.

Theorem ch14p2 P:
  singing_em /\ first_three_laws P /\ cardinal_exists /\ lark_exists
    -> forall x, x!!.
Proof.
  intros [HEM [[HL1 [HL2 HL3]] [[C HC] HLe]]].
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

Theorem ch14p3 P :
  singing_em /\ first_three_laws P
  /\ (exists A, forall x y z, A;x;y;z = x;(z;z);y)
    -> forall x, x!!.
Proof.
  intros [HEM [[HL1 [HL2 HL3]] [A HA]]].
  apply ch14p1. split. apply HEM.
  exists P. repeat split; try assumption.
  intros x. exists (A;P;x;(A;P;x)). intros d.
  rewrite <- HA. easy.
Qed.

Theorem ch14ex1a P :
  singing_em /\ first_three_laws P
    -> forall x, P;x;x!!.
Proof.
  intros [HEM [HL1 [HL2 HL3]]] x d.
  destruct (HEM x d) as [Hxd | Hnxd]; auto.
Qed.

Theorem ch14ex1b P x y :
  singing_em /\ first_three_laws P
  /\ P;y;(P;y;x)!! -> P;y;x!!.
Proof.
  intros [HEM [[HL1 [HL2 HL3]] H]] d.
  destruct (HEM y d) as [Hyd | Hnyd].
  - apply (HL3 y). easy.
  - apply (HL2 y). assumption.
Qed.

Theorem ch14ex1c P x y z :
  singing_em /\ first_three_laws P
  /\ P;x;y!! /\ P;y;z!! -> P;x;z!!.
Proof.
  intros [HEM [[HL1 [HL2 HL3]] [HPxy HPyz]]] d.
  destruct (HEM x d) as [Hxd | Hnxd].
  - specialize (HPxy d). specialize (HPyz d).
    specialize (HL3 x y d (conj Hxd HPxy)) as Hy.
    eauto.
  - eauto.
Qed.

Theorem ch14ex1d P x y z :
  singing_em /\ first_three_laws P
  /\ P;x;(P;y;z)!! -> P;(P;x;y);(P;y;z)!!.
Proof.
  intros [HEM [[HL1 [HL2 HL3]] H]] d.
Admitted.

Theorem ch144ex1e P x y z :
  singing_em /\ first_three_laws P
  /\ P;x;(P;y;z)!! -> P;y;(P;x;z)!!.
Proof.
  intros [HEM [[HL1 [HL2 HL3]] H]] d.
Admitted.