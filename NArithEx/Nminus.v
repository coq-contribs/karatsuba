Require Export NArith.
Require Import TacticEx.
Require Import BinPosEx.
Require Import Pnat.

Definition Nminus x y :=
match x, y with
| x, N0 => x
| N0, _ => N0
| Npos a, Npos b =>
  match (Pcompare a b Eq) with
  | Gt => Npos (Pminus a b)
  | _ => N0
  end
end.

Lemma Nminus_plus: forall p q : N, (Nminus (q + p) q) = p.
Proof.
intros [|a] [|b]; try reflexivity.
simpl.
rewrite Pcompare_refl.
reflexivity.
simpl.
rewrite nat_of_P_gt_Gt_compare_complement_morphism.
rewrite Pminus_plus.
reflexivity.
rewrite nat_of_P_plus_morphism.
destruct (ZL4 a).
rewrite H.
rewrite <- plus_n_Sm.
auto with *.
Qed.

