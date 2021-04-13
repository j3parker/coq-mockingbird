From Mockingbird Require Export Chapter12.

Definition sk_forest := starling_exists /\ kestrel_exists.
Definition ski_forest := sk_forest /\ identity_exists.

Theorem ch18p1 : sk_forest -> ski_forest.
Proof.
  intros [HSe HKe].
  repeat split; try assumption.
  destruct HSe as [S HS].
  destruct HKe as [K HK].
  exists (S;K;K). intros x.
  rewrite HS. repeat rewrite HK. reflexivity.
Qed.

Theorem ch18p2 : ski_forest -> mockingbird_exists.
Proof.
  intros [[[S HS] _] [I HI]].
  exists (S;I;I). intros x.
  rewrite HS. rewrite HI. reflexivity.
Qed.

Theorem ch18p3 : ski_forest ->  thrush_exists.
Proof.
  intros [[[S HS] [K HK]] [I HI]].
Admitted.

Theorem ch18p4 : ski_forest -> bluebird_exists.
Proof.
  intros [[[S HS] [K HK]] [I HI]].
Admitted.