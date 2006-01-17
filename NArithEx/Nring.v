Require Export BinNat.
Require Import Ring.

Open Local Scope N_scope.

Definition NEq x y :=
match (x ?= y) with
|Eq => true
|_ => false
end.

Lemma NEq_eq : forall x y, Is_true (NEq x y) -> x = y.
intros.
apply Ncompare_Eq_eq.
unfold NEq in H.
destruct (x ?= y); 
first [reflexivity | elim H].
Qed.

Definition NRingTheory := Build_Semi_Ring_Theory 
Nplus Nmult 1 NEq 
Nplus_comm Nplus_assoc 
Nmult_comm Nmult_assoc 
Nplus_0_l Nmult_1_l Nmult_0_l
Nmult_plus_distr_r
Nplus_reg_l
NEq_eq.

Add Semi Ring N Nplus Nmult 1 0 NEq NRingTheory 
 [ Npos N0 BinPos.xO BinPos.xI BinPos.xH ].
