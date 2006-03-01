Require Export Nring.
Require Import Ring.
Require Import BinPos.
Require Import BinNat.

Open Local Scope positive_scope.
Open Local Scope N_scope.

Lemma plusMorphism : forall a b, (Npos (a+b)%positive) = (Npos a)+(Npos b).
Proof.
auto.
Qed.

Lemma multMorphism : forall a b, (Npos (a*b)%positive) = (Npos a)*(Npos b).
Proof.
auto.
Qed.

Lemma eqMorphism : forall a b, (Npos a) = (Npos b) -> a = b.
Proof.
congruence.
Qed.

Ltac Pring :=
(try apply eqMorphism);
repeat (rewrite plusMorphism || rewrite multMorphism);
ring.