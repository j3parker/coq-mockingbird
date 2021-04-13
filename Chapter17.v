From Mockingbird Require Export Chapter9.
From Coq Require Import Setoids.Setoid.
From Coq Require Import Logic.Classical_Prop.

Axiom sings : bird -> Prop.
Axiom nightingale : bird -> Prop.

Notation "x !" := (sings x) (at level 60).

Definition law_1 := forall N, nightingale N -> N!.

Definition married x x' := forall y,
  x';y! <-> ~x;y!.

Definition law_2 := forall x, exists x', married x x'.

Definition associated x x' := forall y,
  x';y! <-> x;(y;y)!.

Definition law_3 := forall x, exists x', associated x x'.

Definition law_4 := exists NN, forall x,
  NN;x! <-> nightingale x.

Definition forest_laws := law_1 /\ law_2 /\ law_3 /\ law_4.

Theorem ch17p1 :
  forest_laws -> exists G, G! /\ ~(nightingale G).
Proof.
  intros [H1 [H2 [H3 [NN HNN]]]].
  specialize (H2 NN) as [NN' HNN'].
  specialize (H3 NN') as [NN'x HNN'x].
  pose (G := NN'x;NN'x).
  exists G. destruct (classic (G!)).
  - (* Assume G! *)
    apply HNN'x in H as H'. apply HNN' in H'.
    rewrite HNN in H'.
    (* By construction of G and the definition of N, G must not be a nightingale,
       which is exactly what we were looking for. *)
    easy.
  - (* Assume ~G! *)
    specialize (HNN'x NN'x) as H'; fold G in H'.
    unfold married in *.
    rewrite HNN' in H'. rewrite HNN in H'.
    (* From this we can infer G! <-> ~nightingale G. Either nightingale G and
       we infer G! by the definition of nightingale (a contradiction) or we
       directly get a contradiction. *)
    intuition.
Qed.

(* TODO: pose ch17p2 in a way that doesn't spoil ch17p1 *)

Definition society (S : bird -> Prop) := exists R,
  forall x, S x <-> R;x!.

Lemma ch17p3' S : law_3 /\ society S ->
  (exists A, S A /\ A!) \/ (exists A, ~(S A) /\ ~A!).
Proof.
Admitted.

Theorem ch17p3 : law_2 /\ law_3 -> society sings.
Proof.
Admitted.