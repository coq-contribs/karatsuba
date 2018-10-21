Require Export BinPos.

Local Open Scope positive_scope.

Theorem Pcompare_refl : forall (p:positive) c, Pcompare p p c = c.
intro x; induction x as [x Hrecx| x Hrecx| ]; auto.
Qed.

Lemma Pminus_plus: forall p q : positive, (q + p) - q = p.
Proof.
intros. rewrite Pos.add_comm. now apply Pos.add_sub.
Qed.
