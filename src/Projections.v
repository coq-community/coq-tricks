(**

[Set Printing Projections] is nice if you have records since it shows the fields
using a nice syntax. However, it interacts poorly with classes. See
https://github.com/coq/coq/issues/9814.

*)

Set Printing Projections.

Module point.
Record t :=
  mk { x: nat;
       y: nat; }.

Lemma t_eta : forall (p: t),
  p = {| x := p.(x); y := p.(y) |}.
Proof.
  (* the goal is printed as written above, with projection syntax *)
  destruct p; simpl.
  reflexivity.
Qed.

End point.

Class ToNat T :=
  { to_nat (x:T) : nat; }.

Instance unit_to_nat_instance : ToNat unit :=
  { to_nat _ := 0; }.

(* [Set Printing Projections] causes this to be printed as a projection, even
though we want the instance to be invisible *)
Check (to_nat tt).
(*
unit_to_nat_instance.(to_nat) tt
     : nat
*)

Unset Printing Projections.
(* this is what we want - just [to_nat tt] *)
Check (to_nat tt).
