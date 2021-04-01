From Mockingbird Require Export Chapter9.

Definition sage S := forall x, x <3 (S;x).
Definition sage_exists := exists S, sage S.

Theorem ch10_is_there_a_sage_bird :
  forall M, mockingbird M /\ composition_exists
    /\ (exists A, forall x, composes (A;x) x M)
      -> sage_exists.
Proof.
  intros M [HM [HCe [A HA]]].
  destruct (HCe M A) as [S HS]. exists S. intros x.
  unfold is_fond_of.
  rewrite HS.
  rewrite <- HA.
  rewrite <- HM.
  reflexivity.
Qed.
