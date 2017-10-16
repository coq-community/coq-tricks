Require Import Recdef Div2 Omega FunctionalExtensionality.

(** Counting the number of digits in binary representation. *)

(** Show directly defining this function with Fixpoint is not acceptable.
    Error: Cannot guess decreasing argument of fix. *)
Fail Fixpoint attempt_1 (n r : nat) : nat :=
  match n with
  | 0 => r
  | _ => attempt_1 (Nat.div2 n) (r + 1)
  end.

(** function with decreasing measure. *)
Function attempt_2 (n r : nat) {measure (fun x => x) n} : nat :=
  match n with
  | 0 => r
  | _ => attempt_2 (Nat.div2 n) (r + 1)
  end.
Proof.
  intros. apply lt_div2. omega.
Defined.

Compute attempt_2 1024 0.

(** function with well-founded relation. *)
Print lt.
Function attempt_3 (n r : nat) {wf lt n} : nat :=
  match n with
  | 0 => r
  | _ => attempt_3 (Nat.div2 n) (r + 1)
  end.
Proof.
  + intros. apply lt_div2. omega.
  + apply lt_wf.
Defined.

(** they are totally same. *)
Goal
  attempt_2 8 0 = 4.
Proof.
  (** use [xx_equation] to expand the recursive function. *)
  rewrite attempt_2_equation; simpl.
  rewrite attempt_2_equation; simpl.
  rewrite attempt_2_equation; simpl.
  rewrite attempt_2_equation; simpl.
  rewrite attempt_2_equation; simpl.
  reflexivity.
Qed.