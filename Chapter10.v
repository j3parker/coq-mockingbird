From Mockingbird Require Import Chapter9.

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
