Require Import Nsize.
Require Import Nsplit.
Require Import Nshift.
Require Import Nminus.
Require Import NArith.
Require Import Div2.
Require Import Max.
Require Import Nring.
Require Import Compare.

Tactic Notation "ringreplace" constr (a) "with" constr (b) :=
replace a with b ; [idtac | solve [ ring ]].

Open Local Scope N_scope.

Definition KaratsubaStop : nat := 40%nat.

Fixpoint KaratsubaMultF (i:nat) (a b:N) {struct i} : N :=
 let (a', b') := match (Ncompare a b) with
                 | Lt => (b, a)
                 | _ => (a, b)
                 end in
 let n:=(div2 (Nsize a')) in 
 match i, le KaratsubaStop n with
 | (S i'), true => let (a1,a2):= NsplitAt n a' in
                   let (b1,b2) := NsplitAt n b' in
                   let x := KaratsubaMultF i' a2 b2 in
                   let y := KaratsubaMultF i' a1 b1 in
                   let z := KaratsubaMultF i' (Nplus a1 a2) (Nplus b1 b2)
                   in x + (Nshift n (Nminus z (y+x))) + (Nshift (2*n) y)
 | _, _ => (Nmult a' b')
end.

Definition KaratsubaMult a b := KaratsubaMultF (max (Nsize a) (Nsize b)) a b.

Lemma KaratsubaMultCorrect1 : forall (a b c d:N),
(Nminus ((a + b) * (c + d)) (a * c + b * d))=(b*c + a*d).
Proof.
intros.
ringreplace ((a + b) * (c + d)) with ((a*c + b*d) + (b * c + a * d)).
apply Nminus_plus.
Qed.

Theorem KaratsubaMultCorrect : forall a b, KaratsubaMult a b = a * b.
Proof.
intros a b.
unfold KaratsubaMult.
generalize (max (Nsize a) (Nsize b)).
intros i.
generalize a b.
clear a b.
induction i; intros a b.
simpl.
destruct (a ?= b); ring.
Opaque KaratsubaStop.
simpl.
set (p:=match a ?= b with
     | Eq => (a, b)
     | Lt => (b, a)
     | Gt => (a, b)
     end).
replace (a*b) with ((fst p)*(snd p)).
destruct p.
simpl.
Transparent KaratsubaStop.
destruct (le KaratsubaStop (div2 (Nsize n))).
transitivity ((let (a0, b0) := NsplitAt (div2 (Nsize n)) n in
 b0 + Nshift (div2 (Nsize n)) a0) *
(let (a0, b0) := NsplitAt (div2 (Nsize n)) n0 in
 b0 + Nshift (div2 (Nsize n)) a0)).
destruct (NsplitAt (div2 (Nsize n)) n).
destruct (NsplitAt (div2 (Nsize n)) n0).
repeat rewrite IHi.
rewrite KaratsubaMultCorrect1.
autorewrite with NshiftExpand.
change (Npos (Pshift.Pow2 0)) with 1.
ring.
rewrite (NsplitAtSum (div2 (Nsize n)) n).
rewrite (NsplitAtSum (div2 (Nsize n)) n0).
reflexivity.
reflexivity.
destruct (a?=b); try reflexivity.
apply Nmult_comm.
Qed.
