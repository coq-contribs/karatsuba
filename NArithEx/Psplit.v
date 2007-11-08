Require Export BinNat.
Require Export Psize. 
Require Export Pshift.
Require Import TacticEx.
Require Import Arith.

Coercion Local Npos:positive>->NBinDefs.N.

Definition PsplitAt (n:nat) (x:positive) : n < Psize x -> positive*N.
fix 1.
destruct n.
intros.
exact (x, N0).
intros.
destruct x.
simpl in H.
assert (n < Psize x);
auto with *.
destruct (PsplitAt _ _ H0).
exact (p, Ndouble_plus_one n0).
simpl in H.
assert (n < Psize x);
auto with *.
destruct (PsplitAt _ _ H0).
exact (p, Ndouble n0).
elimtype False.
clear PsplitAt.
abstract (inversion H; inversion H1).
Defined.

Open Local Scope N_scope.

Lemma PsplitAt1 : forall n x (H:(n < Psize x)%nat), (let s:=PsplitAt n x H in (snd s)+(Pshift n (fst s)))=x.
Proof.
induction n.
auto.
intros.
destruct x; simpl in *; try
(dcase (PsplitAt n x (lt_S_n n (Psize x) H)); intros;
pose (IHn _ (lt_S_n n (Psize x) H));
rewrite H0 in e;
destruct n0;
(simpl in *;
congruence)).
inversion H.
inversion H1.
Qed.

Definition PsplitAt2 : forall (n:nat) (x:positive) (Hlt:(n < Psize x)%nat),
 match (snd (PsplitAt n x Hlt)) with
 | N0 => True
 | Npos x => ((Psize x) <= n)%nat
 end.
Proof.
induction n.
constructor.
intros; 
destruct x;
simpl in *; try(
pose (IHn _ (lt_S_n n (Psize x) Hlt));
dcase (PsplitAt n x (lt_S_n n (Psize x) Hlt)); intros;
rewrite H in y;
simpl in *;
destruct n0;
simpl;
auto with *).
inversion Hlt.
inversion H0.
Qed.

Definition PsplitAt3 : forall (n:nat) (x:positive) (Hlt:(n < Psize x)%nat),
 (n+(Psize (fst (PsplitAt n x Hlt))))%nat = (Psize x).
Proof.
induction n;
intros.
reflexivity.
destruct x; try (
pose (IHn _ (lt_S_n n (Psize x) Hlt));
dcase (PsplitAt n x (lt_S_n n (Psize x) Hlt)); intros;
rewrite H in e;
simpl in *;
rewrite H;
simpl in *;
rewrite e;
reflexivity).
inversion Hlt.
inversion H0.
Qed.

Fixpoint PsplitAtFast (n:nat) (x:positive) {struct n} : positive * N := 
 match n with
  | O => (x, 0%N)
  | S n0 =>
      match x with
      | xI x0 =>
          let (p0, n1) := PsplitAtFast n0 x0
          in (p0, Ndouble_plus_one n1)
      | xO x0 =>
          let (p0, n1) := PsplitAtFast n0 x0 
          in (p0, Ndouble n1)
      | xH => (xH,N0) (* Garbage *)
      end
  end.

Lemma PsplitAtFastCorrect : forall n x (H:(n < Psize x)%nat), (PsplitAtFast n x) = (PsplitAt n x H).
Proof.
induction n; intros.
reflexivity.
simpl.
destruct x; try(rewrite <- IHn; reflexivity).
destruct (PsplitAt_subproof n H).
Qed.
