Require Import Recdef Div2 Omega FunctionalExtensionality.

(** [foo] and [bar] count the number of digits in binary representation. *)

(** Error: Cannot guess decreasing argument of fix. *)
Fail Fixpoint foo (n : nat) (b : bool) : nat :=
  match n with
  | 0 => 42
  | S n' => if b then foo n false else foo n' true
  end.

(** function with decreasing measure. *)
Function foo (n r : nat) {measure (fun x => x) n} : nat :=
  match n with
  | 0 => r
  | _ => foo (Nat.div2 n) (r + 1)
  end.
Proof.
  intros. apply lt_div2. omega.
Defined.

Compute foo 1024 0.

(** function with well-founded relation. *)
Print lt.
Function bar (n r : nat) {wf lt n} : nat :=
  match n with
  | 0 => r
  | _ => bar (Nat.div2 n) (r + 1)
  end.
Proof.
  + intros. apply lt_div2. omega.
  + apply lt_wf.
Defined.

(** they are totally same. *)
Goal
  foo = bar.
Proof.
  extensionality n.
  extensionality r.
  induction n using lt_wf_ind.
  (** use [xx_equation] to expand the recursive function. *)
  rewrite (foo_equation n r).
  rewrite (bar_equation n r).
  destruct n; auto.
Qed.
