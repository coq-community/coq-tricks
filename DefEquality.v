Local Tactic Notation "unfolded_eq" constr(pf) :=
  let x := (eval red in pf) in
  exact (eq_refl : (pf = x)).

Notation unfolded_eq pf := ltac:(unfolded_eq pf) (only parsing).

Module Example.
  Definition foo x y z := x + y + z.
  Definition foo_eq := unfolded_eq foo.
  Check foo_eq.
  (*
  foo_eq
     : foo = (fun x y z : nat => x + y + z)
   *)
End Example.
