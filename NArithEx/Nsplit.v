Require Export BinNat.
Require Import Nshift.
Require Import BinPos.
Require Import TacticEx.

Fixpoint PsplitAt (n:nat) (x:positive) {struct n} : N * N := 
 match n with
  | O => (Npos x, 0%N)
  | S n0 =>
      match x with
      | xI x0 =>
          let (p0, n1) := PsplitAt n0 x0
          in (p0, Ndouble_plus_one n1)
      | xO x0 =>
          let (p0, n1) := PsplitAt n0 x0 
          in (p0, N.double n1)
      | xH => (N0,Npos x)
      end
  end.

Local Open Scope N_scope.

Lemma PsplitAtSum : forall n x , (let (a,b):=PsplitAt n x in b+(Nshift n a))=(Npos x).
Proof.
induction n.
auto.
intros.
destruct x; simpl in *; try (
dcase (PsplitAt n x); intros;
pose (IHn x);
rewrite H in e;
destruct n0; destruct n1;
simpl in *;
congruence).
reflexivity.
Qed.

Definition NsplitAt (n:nat) (x:N) : N*N :=
match x with
| N0 => (N0, N0)
| (Npos xp) => PsplitAt n xp
end.

Lemma NsplitAtSum : forall n x , (let (a,b):=NsplitAt n x in b+(Nshift n a))=x.
Proof.
intros.
destruct x.
reflexivity.
apply (PsplitAtSum n p).
Qed.
