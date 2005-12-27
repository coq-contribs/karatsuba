Require Import utf8.
Require Import Coercions.

(** This module provides a basis for the theory of decidable orders.
 *)
(** Right now it defines min and max functions, and contains the
     framework and some example theorems of min and max.
 *)

(** A decideable order is a total order that is decidable.  Here is the
     signature.
  *)
Module Type Sig.
Parameter A : Type.
Parameter le : A ⇒ A ⇒ bool.

Infix "≤" := le : order_scope.
Open Scope order_scope.

Axiom le_refl : ∀ x, x ≤ x.
Axiom le_antisym : ∀ x y, x ≤ y ⇒ y ≤ x ⇒ x = y.
Axiom le_trans : ∀ x y z, x ≤ y ⇒ y ≤ z ⇒ x ≤ z.
Axiom le_total : ∀ x y, {x ≤ y} + {y ≤ x}.
End Sig.

(** When the operands of ≤ are reversed, the result is the dual
    decidable order.  This functor module takes a decidable order to its
    dual order.  This is used to create dual theorems about min and max
    for free.
 *)
Module Dual (Ord : Sig) <: Sig.
Definition A := Ord.A.
Definition le a b : bool := Ord.le b a.

Infix "≤" := le : order_scope.
Open Scope order_scope.

Definition le_refl := Ord.le_refl.

Lemma le_antisym : ∀ x y, x ≤ y ⇒ y ≤ x ⇒ x=y.
Proof.
unfold le.
set (H:=Ord.le_antisym).
auto.
Qed.

Lemma le_trans : ∀ x y z, x ≤ y ⇒ y ≤ z ⇒ x ≤ z.
Proof.
unfold le.
intuition.
apply Ord.le_trans with y; assumption.
Qed.

Lemma le_total : ∀ x y, {x ≤ y} + {y ≤ x}.
Proof.
unfold le.
set (H:=Ord.le_total).
auto.
Defined.

End Dual.

(** This module defines the min function, and some basic properties of min.
 *)
Module Min (Ord : Sig).
Import Ord.

Hint Resolve le_refl.
Hint Resolve le_antisym.

Definition min a b : A := if (le a b) then a else b.

Lemma case_min : ∀ P : A ⇒ Type, ∀ x y, (x ≤ y ⇒ P x) ⇒ (y ≤ x ⇒ P y) ⇒ P (min x y).
Proof.
intros.
unfold min.
destruct (le_total x y).
destruct (le x y).
auto.
contradiction.
destruct (le x y).
simpl in *.
auto.
auto.
Qed.

Lemma min_glb : ∀ x y z, z ≤ x ⇒ z ≤ y ⇒ z ≤ min x y.
Proof.
intros.
apply case_min; tauto.
Qed.

Lemma min_left : ∀ x y, min x y ≤ x.
Proof.
intros.
apply case_min; auto.
Qed.

Lemma min_right : ∀ x y, min x y ≤ y.
Proof.
intros.
apply case_min; auto.
Qed.

Lemma min_sym : ∀ x y, min x y = min y x.
Proof.
intros.
do 2 apply case_min; auto.
Qed.

Lemma min_assoc : ∀ x y z, min (min x y) z = min x (min y z).
Proof.
intros.
set (H0 := le_trans x z y).
set (H1 := le_trans x y z).
set (H2 := le_trans z y x).
set (H3 := le_trans z x y).
repeat apply case_min; auto.
Qed.

End Min.

(** This module defines the max function as the dual of the min function.
    All the theorems about min are dualized to produce theorems about max.
 *)
Module Max (Ord : Sig).
Import Ord.
Module DualOrd := Dual Ord.
Module Max := Min DualOrd.

Definition max := Max.min.
Definition case_max : ∀ P : A ⇒ Type, ∀ x y, (y ≤ x ⇒ P x) ⇒ (x ≤ y ⇒ P y) ⇒ P (max x y) := Max.case_min.
Definition max_lub : ∀ x y z, x ≤ z ⇒ y ≤ z ⇒ max x y ≤ z := Max.min_glb.
Definition max_left : ∀ x y, x ≤ (max x y) := Max.min_left.
Definition max_right : ∀ x y, y ≤ (max x y) := Max.min_right.
Definition max_sym : ∀ x y, max x y = max y x := Max.min_sym.
Definition max_assoc : ∀ x y z, max (max x y) z = max x (max y z) := Max.min_assoc .
End Max.

(** This module exports both the min and max theories.
 *)
Module MinMax (Ord : Sig).
Export Ord.

Module MinOrd := Min Ord.
Export MinOrd.

Module MaxOrd := Max Ord.
Export MaxOrd.
End MinMax.

(** This module defines half of the disributive laws between min and max.
 *)
Module DistributivityA (Ord : Sig).

Module MinMaxOrd := MinMax Ord.
Import MinMaxOrd.

Lemma min_max_distr : ∀ x y z, (min x (max y z))=(max (min x y) (min x z)).
Proof.
intros.
set (H:=le_antisym).
set (H0:=(le_trans x y z)).
set (H1:=(le_trans x z y)).
set (H2:=(le_trans z x y)).
set (H3:=(le_trans y x z)).
repeat apply case_min; repeat apply case_max; auto.
Qed.

End DistributivityA.

(** This module defines the other half of the distributive laws about min and max.
    These other laws are the duals of the previous distributive laws
*)
Module DistributivityB (Ord : Sig).

Module MinMaxOrd := MinMax Ord.
Import MinMaxOrd.

Module DualOrd := Dual Ord.
Module DualDistrib := DistributivityA DualOrd.

Definition max_min_distr : ∀ x y z, (max x (min y z))=(min (max x y) (max x z)) := DualDistrib.min_max_distr.

End DistributivityB.

(** This module combines the two modules about distributivity into one.
 *)
Module Distributivity  (Ord : Sig).

Module MinMaxOrd := MinMax Ord.
Export MinMaxOrd.

Module DistributivityAOrd := DistributivityA Ord.
Export DistributivityAOrd.

Module DistributivityBOrd := DistributivityB Ord.
Export DistributivityBOrd.

End Distributivity.

(** This module combines all the modules about the theory of decidable orders
    into one module.
 *)
Module Theory (Ord : Sig).

Module DistributivityOrd := Distributivity Ord.
Export DistributivityOrd.

End Theory.
