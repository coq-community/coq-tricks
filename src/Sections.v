Require Import Setoid.
Set Implicit Arguments.

(** Example of using sections, notations, and implicit types together. *)

Section Memory.
  Context (A V:Type).
  Definition mem := A -> option V.
  Implicit Types (m:mem) (a:A) (v:V).

  Definition empty : mem :=
    fun _ => None.

  Definition disjoint m1 m2 :=
    forall x v, m1 x = Some v -> forall v', m2 x = Some v' -> False.

  Global Instance disjoint_symmetric : Symmetric disjoint.
  firstorder.
  Qed.
End Memory.

Section MoreMem.
  Context {A V:Type}.
  Notation mem := (mem A V).
  Implicit Types (m:mem) (a:A) (v:V).

  Context {Aeq: forall (x y:A), {x=y} + {x<>y}}.

  (* this uses the Symmetric instance from above *)
  Theorem disjoint_sym m1 m2 :
    disjoint m1 m2 <-> disjoint m2 m1.
  Proof.
    split; symmetry; auto.
  Qed.

  Definition upd m a0 v : mem :=
    fun a => if Aeq a0 a then Some v else m a.

  Theorem upd_eq m a v : upd m a v a = Some v.
  Proof.
    unfold upd.
    destruct (Aeq a a); congruence.
  Qed.

  Definition upd_ne m a v a' :
    a <> a' ->
    upd m a v a' = m a'.
  Proof.
    unfold upd; intros.
    destruct (Aeq a a'); congruence.
  Qed.
End MoreMem.
