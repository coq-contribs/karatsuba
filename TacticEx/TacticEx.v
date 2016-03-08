Ltac dcase x := generalize (refl_equal x); pattern x at -1; case x.

Ltac applyFwd l :=
first
[refine l
|refine (proj1 l _)
|refine (l _)
|refine (proj1 (l _) _)
|refine (l _ _)
|refine (proj1 (l _ _) _)
|refine (l _ _ _)
|refine (proj1 (l _ _ _) _)
|refine (l _ _ _ _)
|refine (proj1 (l _ _ _ _) _)
|refine (l _ _ _ _ _)
|refine (proj1 (l _ _ _ _ _) _)
|refine (l _ _ _ _ _ _)
|refine (proj1 (l _ _ _ _ _ _) _)
|refine (l _ _ _ _ _ _ _)
|refine (proj1 (l _ _ _ _ _ _ _) _)
|refine (l _ _ _ _ _ _ _ _)
].

Ltac applyRev l :=
first
[refine (proj2 l _)
|refine (proj2 (l _) _)
|refine (proj2 (l _ _) _)
|refine (proj2 (l _ _ _) _)
|refine (proj2 (l _ _ _ _) _)
|refine (proj2 (l _ _ _ _ _) _)
|refine (proj2 (l _ _ _ _ _ _) _)
|refine (proj2 (l _ _ _ _ _ _ _) _)
].

Ltac LHS :=
match goal with
| |-(?a = _) => constr:(a)
| |-(_ ?a _) => constr:(a)
end.

Ltac RHS :=
match goal with
| |-(_ = ?a) => constr:(a)
| |-(_ _ ?a) => constr:(a)
end.

Ltac decideEquality :=
match goal with
| |- forall x y, {x = y}+{~x=y} => decide equality
| |- {?a=?b}+{~?a=?b} => decide equality
| |- {~?a=?b}+{?a=?b} => cut ({a=b}+{~a=b});[tauto | decide equality]
end.
