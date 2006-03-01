Require Export BinInt.
Require Import BinNat.
Require Import Karatsuba.

Definition Zmult x y := 
match x, y with
|Z0, _ => Z0
|_, Z0 => Z0
|(Zpos x'), (Zpos y') => Z_of_N (KaratsubaMult (Npos x') (Npos y'))
|(Zpos x'), (Zneg y') => Zopp (Z_of_N (KaratsubaMult (Npos x') (Npos y')))
|(Zneg x'), (Zpos y') => Zopp (Z_of_N (KaratsubaMult (Npos x') (Npos y')))
|(Zneg x'), (Zneg y') => Z_of_N (KaratsubaMult (Npos x') (Npos y'))
end.

Theorem ZmultCorrect : forall x y, (Zmult x y)=(BinInt.Zmult x y).
Proof.
intros.
destruct x; destruct y; try reflexivity;
simpl;
rewrite KaratsubaMultCorrect;
reflexivity.
Qed.