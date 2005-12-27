Require Import BinNat.
Require Import Karatsuba.

Definition A : N := 11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111%N.

Time Eval lazy beta delta iota zeta in A.
Time Eval compute in (KaratsubaMult A A).
Time Eval compute in (Nmult A A).

Time Eval lazy beta delta iota zeta in (KaratsubaMult A A).
Time Eval lazy beta delta iota zeta in (Nmult A A).
