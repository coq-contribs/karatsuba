Require Import Coercions.

Definition comparisonLt a : bool :=
match a with
| Lt => true
| Eq => false
| Gt => false
end.

Definition comparisonLe a : bool :=
match a with
| Lt => true
| Eq => true
| Gt => false
end.

Definition comparisonGt a : bool :=
match a with
| Lt => false
| Eq => false
| Gt => true
end.

Definition comparisonGe a : bool :=
match a with
| Lt => false
| Eq => true
| Gt => true
end.

Lemma compareLt : forall a, comparisonLt a -> a=Lt.
Proof.
induction a; auto; contradiction.
Qed.

Lemma compareLe : forall a, comparisonLt a -> {a=Lt}+{a=Eq}.
Proof.
induction a; auto; contradiction.
Qed.
