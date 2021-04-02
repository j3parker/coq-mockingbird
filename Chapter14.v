From Mockingbird Require Export Chapter11.

Axiom day : Type.
Axiom sings : bird -> day -> Prop.

Notation "x , d !" := (sings x d) (at level 60).

Definition law_1 P := forall x y d,
  y,d! -> P;x;y,d!.

Definition law_2 P := forall x y d,
  ~x,d! -> P;x;y,d!.

Definition law_3 P := forall x y d,
  x,d! /\ P;x;y,d! -> y,d!.

Definition law_4 P := forall x, exists y, forall d,
  y,d! <-> P;y;x,d!.

Definition special P :=
  law_1 P /\ law_2 P /\ law_3 P /\ law_4 P.

Definition all_birds_sing_on_all_days :=
  forall x d, x,d!.

Theorem ch14p1 P :
  special P -> all_birds_sing_on_all_days.
Proof.
  unfold special;
  unfold law_1; unfold law_2; unfold law_3; unfold law_4;
  intros [H1 [H2 [H3 H4]]] x d.
  apply (H3 x).
Admitted.

Definition special' P :=
  law_1 P /\ law_2 P /\ law_3 P.

Theorem ch14p2 P :
  special' P /\ lark_exists -> ~all_birds_sing_on_all_days.
Proof.
  intros [[H1 [H2 H3]] HLe] H.
Admitted.

Theorem ch14p2' P :
  special' P /\ cardinal_exists -> ~all_birds_sing_on_all_days.
Proof.
  intros [[H1 [H2 H3]] HCe] H.
Admitted.

Theorem ch14p2'' P :
  special' P /\ cardinal_exists /\ lark_exists
    -> all_birds_sing_on_all_days.
Proof.
  intros [[H1 [H2 H3]] [HCe HLe]] x d.
Admitted.

(* TODO: p3 *)