Require Import Comparison.
Require Import ComparisonDecOrd.

Module natComparision <: ComparisonSig.

Definition A := nat.

Fixpoint compare (a b : nat) {struct a} : comparison :=
match a,b with
| O, O => Eq
| O, _ => Lt
| _, O => Gt
| (S a'), (S b') => compare a' b'
end.

Infix "?=" := compare (at level 70) : nat_scope.

Lemma compare_refl : forall a b, a ?= b = Eq <-> a = b.
Proof.
intros.
split.
generalize b.
clear b.
induction a; induction b; intros; try discriminate H.
reflexivity.
rewrite IHa with b.
reflexivity.
apply H.
intros.
subst.
induction b.
reflexivity.
apply IHb.
Qed.

Lemma compare_antisym : forall a b, CompOpp (a ?= b) = (b ?= a).
Proof.
induction a; induction b; intros; try reflexivity.
simpl.
apply IHa.
Qed.

Lemma compare_trans : forall a b c, 
(a ?= b) = (b ?= c) -> (a ?= b) = (a ?= c) /\ (b ?= c) = (a ?= c).
Proof.
apply trans_simp.
induction x; induction y; induction z; intros; auto.
rewrite <- (compare_antisym 0 (S y)) in H.
destruct (0 ?= S y); try discriminate H.
auto.
discriminate H.
simpl.
apply IHx.
apply H.
Qed.

End natComparision.

Module natDecOrd <: DecidableOrder.Sig := CompareDecOrd natComparision.
Export natDecOrd.
