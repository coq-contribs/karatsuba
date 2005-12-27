Require Import Pshift.
Require Export BinNat.

Definition Nshift (n:nat) (x:N) : N :=
match x with 
| N0 => N0
| (Npos xp) => Npos (Pshift n xp)
end.

Lemma Nshift2 : forall x n m, (Nshift n (Nshift m x))=(Nshift (n+m) x).
Proof.
destruct x.
auto.
simpl.
intros.
rewrite Pshift2.
reflexivity.
Qed.

Lemma NshiftExpand : forall x n, (Nshift n x)= ((Npos (Pow2 n))*x)%N.
Proof.
destruct x.
reflexivity.
intros.
simpl.
rewrite PshiftExpand.
reflexivity.
Qed.

Hint Rewrite NshiftExpand : NshiftExpand.
Hint Rewrite <- Nshift2 : NshiftExpand.
