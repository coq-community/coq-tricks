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
Function attempt_3 (n r : nat) {wf lt n} : nat :=
  match n with
  | 0 => r
  | _ => attempt_3 (Nat.div2 n) (r + 1)
  end.
Proof.
  + intros. apply lt_div2. omega.
  + apply lt_wf.
Defined.

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

(* note that the two above definitions are really just alternate ways of doing
the same thing ([measure] is just a convenience for leveraging the
well-foundedness of [nat]'s [lt]) *)
Theorem attempts_2_and_3_are_the_same :
  attempt_2 = attempt_3.
Proof.
  reflexivity.
Qed.

(** Now we'll redo the above using the standard library's [Fix] combinator,
which provides general well-founded recursion.

 See CPDT's chapter http://adam.chlipala.net/cpdt/html/GeneralRec.html for an
 excellent overview, including a better description of how this approach itself
 works under the hood. *)
Check Fix.
(*
Fix
     : forall (A : Type) (R : A -> A -> Prop),
       well_founded R ->
       forall P : A -> Type,
       (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
       forall x : A, P x

To read this, start at the bottom: we're writing a function of type [forall (x:A), P
x]. The recursion is over [A] and decreases the relation [R], which must be
well-founded (think of [A = nat] and [R = lt] as examples). The body of the
function has the type

[forall (x:A) (F: forall (y:A), R y x -> P y), P x]

[x] is simply the argument to the body. The second argument is what I've called
[F] here: think of this as being the function being defined itself, in order to
support recursion. The catch is in its signature: instead of just taking [y:A],
it also takes [R y x]; that is, in order to call [F] recursively, you must pass
a proof that the argument used is smaller than the outer argument [x]. Because
[R] is well-founded, eventually this body must stop calling itself recursively.
 *)

Lemma div2_smaller : forall n n',
    n = S n' ->
    Nat.div2 n < n.
Proof.
  destruct n; intros.
  discriminate.
  apply lt_div2; omega.
Qed.

Definition numdigits (n: nat) : nat.
  refine
    (Fix lt_wf (fun _ => nat)
         (fun n (numdigits: forall (n':nat), n' < n -> nat) =>
            (* unfortunately we need to convoy a proof to keep track of the
            value of [n] when proving we decrease the argument to [numdigits] *)
            match n as n0 return (n = n0 -> nat) with
            | 0 => fun _ => 0
            | S n' => fun H => 1 + numdigits (Nat.div2 n) _
            end eq_refl) n).
  eapply div2_smaller; eauto.
Defined.

(* We need to provide a wrapper around the standard library's [Fix_eq], which
describes the computational behavior of a [Fix] as being the same as a one-step
unfolding. However, the theorem also requires one to prove the body is unable to
distinguish between [F] arguments that are extensionally equal; this is true of
any Gallina code but can't be proven within Coq once and for all. *)
Theorem numdigits_eq : forall n,
    numdigits n = match n with
                  | 0 => 0
                  | _ => 1 + numdigits (Nat.div2 n)
                  end.
Proof.
  intros.
  match goal with
  | [ |- ?lhs = _ ] =>
    match eval unfold numdigits in lhs with
    | Fix ?wf ?P ?F _ =>
      rewrite (Fix_eq wf P F)
    end
  end.
  destruct n; reflexivity.

  intros.
  destruct x; auto.
Qed.

Example numdigits_5 : numdigits 8 = 4.
Proof.
  repeat (rewrite numdigits_eq; cbn [Nat.div2 plus]).
  reflexivity.
Qed.
