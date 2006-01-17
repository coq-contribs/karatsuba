Require Export BinPos.

Fixpoint Pshift (n:nat) (x:positive) {struct n} : positive :=
match n with 
| O => x
| (S m) => xO (Pshift m x)
end.

Definition Pow2 (n:nat) := Pshift n 1.

Open Local Scope positive_scope.

Lemma Pshift1 : forall x y n, (Pshift n x)*y=(Pshift n (x*y)).
Proof.
induction n;
simpl;
congruence.
Qed.

Lemma Pshift2 : forall x n m, (Pshift n (Pshift m x))=(Pshift (n+m) x).
Proof.
induction n;
simpl;
intros;
try rewrite IHn;
reflexivity.
Qed.

Lemma Pshift3 : forall x y n, (Pshift n x)+(Pshift n y)=(Pshift n (x+y)).
Proof.
induction n;
simpl;
congruence.
Qed.

Lemma PshiftExpand : forall x n, (Pshift n x)= (Pow2 n)*x.
Proof.
intros.
unfold Pow2.
rewrite Pshift1.
reflexivity.
Qed.

Hint Rewrite PshiftExpand : PshiftExpand.
Hint Rewrite <- Pshift2 : PshiftExpand.