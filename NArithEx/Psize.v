Require Import Arith.
Require Export BinPos.

Fixpoint Psize (x:positive) : nat :=
match x with
 xH => S 0
|xO y => S (Psize y)
|xI y => S (Psize y)
end.

Lemma Psize1 : forall x y, {Psize (x+y) <= S (Psize x)}+{Psize (x+y) <= S (Psize y)}.
Proof.
pose le_n_S.
assert (forall x, Psize (Pos.succ x) <= S (Psize x)).
induction x; simpl in *; auto with *.
assert (forall x y : positive,
({Psize (x + y) <= S (Psize x)} + {Psize (x + y) <= S (Psize y)}) *
({Psize (Pplus_carry x y) <= S (Psize x)} + {Psize (Pplus_carry x y) <= S (Psize y)})).
induction x; destruct y ;
  (try destruct (IHx y) as [[s0|s0] [s1|s1]] ; repeat split ; simpl ; auto). 
intros. destruct (H0 x y) as [[s0|s0] [s1|s1]]; auto.
Qed.
