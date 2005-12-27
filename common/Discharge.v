Inductive prodTactic (A : Type) (B : Type) : Type :=  pairTactic : A -> B -> prodTactic A B.
Implicit Arguments pairTactic [A B].
Inductive unitTactic : Type := ttTactic : unitTactic.

Notation "[ x , y , .. , z ]" := (pairTactic .. (pairTactic x y) .. z) (at level 1) : tactic_scope.

Open Scope tactic_scope.

Ltac taclistFwd tac l :=
match type of l with
|(prodTactic _ _) =>
 match l with 
 |(pairTactic ?y ?a) => taclistFwd tac y; taclistFwd tac a
 end
|_=>tac l
end.

Ltac taclistRev tac l :=
match type of l with
|(prodTactic _ _) =>
 match l with 
 |(pairTactic ?y ?a) => taclistRev tac a; taclistRev tac y
 end
|_=>tac l
end.

Ltac discharge x :=
 let dischargeOne a := generalize a; clear a in
  taclistRev dischargeOne x.

Ltac gen expr lst :=
match type of lst with
|(prodTactic _ _) =>
 match lst with
 |(pairTactic ?p ?q) => let first := gen expr q in gen first p
 end
|_ => 
  match (eval pattern lst in expr) with
    (?f ?z) => 
     let Z := type of lst
     in  constr:(forall n:Z, f n)
  end
end.

Ltac introNames := 
match goal with
H : unitTactic |- _ => clear H; intro H; introNames
|_ => idtac
end.

Ltac wlog nn expr lst :=
match goal with 
| |- ?g =>
 let full := gen (expr -> g) lst in 
 cut full;
 [intro | let c x := clear x; pose (x:=ttTactic) in taclistRev c lst; introNames; intro nn]
end.

(*
Goal forall a b c:nat, a + b = c.
intros.
wlog (0<a/\0<b) [a,b].
Show 2.
discharge [c,b,a].

Goal forall a b c:nat, {a<b}+{b< a} ->{c : nat | a + b = c}.
intros.
discharge c.
discharge {b,a, H}.
*)