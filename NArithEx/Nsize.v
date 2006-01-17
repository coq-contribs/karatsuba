Require Export BinNat.
Require Import Psize.

Definition Nsize x :=
match x with
| N0 => 0
| (Npos xp) => Psize xp
end.