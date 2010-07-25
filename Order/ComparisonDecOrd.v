Require Import utf8.
Require Import TacticEx.
Require Import Discharge.
Require Import Coercions.

Require Import Comparison.
Require DecidableOrder.

Lemma trans_simp : ∀ A B : Type, ∀ R : A ⇒ A ⇒ B, 
(∀ x y z, (R x y) = (R y z) ⇒ {(R x y) = (R x z)} + {(R y z) = (R x z)}) ⇒
∀ x y z, (R x y) = (R y z) ⇒ (R x y) = (R x z) ∧ (R y z) = (R x z).
Proof.
intros.
split;
induction (X x y z);
congruence.
Qed.

Module Type ComparisonSig.
Parameter A : Type.
Parameter compare : A ⇒ A ⇒ comparison.

Infix "?=" := compare (at level 70) : order_scope.
Open Scope order_scope.

Axiom compare_refl : ∀ x y, x ?= y = Eq ⇔ x = y.
Axiom compare_antisym : ∀ x y, CompOpp (x ?= y) = (y ?= x).
Axiom compare_trans : ∀ x y z, (x ?= y) = (y ?= z) ⇒ (x ?= y) = (x ?= z) ∧ (y ?= z) = (x ?= z).

End ComparisonSig.

Module CompareDecOrd (M : ComparisonSig) <: DecidableOrder.Sig.

Definition A :Type := M.A.
Definition le (x y : A) : bool := comparisonLe (M.compare x y).

Infix "≤" := le : order_scope.
Open Scope order_scope.

Lemma le_refl : ∀ x, x ≤ x.
Proof.
intros.
unfold le.
replace (M.compare x x) with Eq.
constructor.
symmetry.
applyRev M.compare_refl.
reflexivity.
Qed.

Lemma le_antisym : ∀ x y, x ≤ y ⇒ y ≤ x ⇒ x = y.
Proof.
unfold le.
intros.
applyFwd M.compare_refl.
pose (M.compare_antisym x y).
discharge [H, H0, e].
induction (M.compare x y); intros.
reflexivity.
rewrite <- e in H0.
elim H0.
elim H.
Qed.

Lemma le_trans : ∀ x y z, x ≤ y ⇒ y ≤ z ⇒ x ≤ z.
Proof.
unfold le.
intros x y z.
pose (s := (M.compare_trans x y z)).
discharge s.
pose (s := (M.compare_refl x y)).
discharge s.
pose (s := (M.compare_refl y z)).
discharge s.
dcase (M.compare x y); dcase (M.compare y z);
intros; 
try elim H1; try elim H2;
try (destruct (s1 (refl_equal _)); rewrite <- H3; constructor).
replace x with y.
rewrite H.
constructor.
firstorder.
replace z with y.
rewrite H0.
constructor.
firstorder.
Qed.

Lemma le_total : ∀ x y, {x ≤ y} + {y ≤ x}.
Proof.
intros.
unfold le.
rewrite <- (M.compare_antisym x y).
induction (M.compare x y);
simpl;
auto.
Defined.

End CompareDecOrd.
