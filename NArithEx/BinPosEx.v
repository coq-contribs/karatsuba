Require Export BinPos.

Open Local Scope positive_scope.

Theorem Pcompare_refl : forall (p:positive) c, (p ?= p) c = c.
intro x; induction x as [x Hrecx| x Hrecx| ]; auto.
Qed.

Lemma Pplus_bigger : forall (p q:positive) c, (q + p ?= q) c=Gt.
Proof.
assert (forall x c, (Psucc x ?= x) c = Gt).
induction x; intros; simpl in *.
apply IHx.
apply Pcompare_refl.
reflexivity.
assert (forall (p q : positive) (c : comparison), 
 ((q + p ?= q) c = Gt /\ (Pplus_carry q p ?= q) c = Gt)).
intro x; induction x; intros y c; destruct y as [y| y| ]; split; simpl in |- *;
reflexivity || firstorder || apply Pcompare_refl.
firstorder.
Qed.

Lemma Pminus_plus: forall p q : positive, (q + p) - q = p.
Proof.
intros.
apply Pplus_reg_l with q.
apply Pplus_minus.
apply Pplus_bigger.
Qed.
