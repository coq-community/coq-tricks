Require Import RelationClasses.
(* The classes in RelationClasses are useful to implement. Implementing
[PreOrder] will make the [reflexivity], [transitivity], and [etransitivity]
tactics work with your own relations (much better than manually figuring out
which transitivity lemma to apply!). Here's a nice way to make implementing
relation classes more convenient. *)

Ltac RelInstance_t :=
  intros;
  let refl := try solve [ hnf; intros; reflexivity ] in
  let trans := try solve [ hnf; intros; etransitivity; eauto ] in
  try match goal with
  | |- Reflexive _ =>
    hnf; intros; refl
  | |- Transitive _ =>
    hnf; intros; trans
  | |- PreOrder _ =>
    constructor; hnf; intros; [ refl | trans ]
  end.

Definition funext_eq A B (f1 f2: A -> B) := forall x, f1 x = f2 x.

Section Method1.
  (* the most basic way to provide an instance *)
  Instance funext_eq_PreOrder1 A B : PreOrder (funext_eq A B).
  Proof.
    RelInstance_t.
  Qed.
End Method1.

(* we can use tactics-in-terms with notations to create a term-like definition
that is actually a tactic *)
Notation RelInstance := (ltac:(RelInstance_t)) (only parsing).

Section Method2.
  (* this is more powerful than it looks - if [RelInstance] had not solved the
  goal, you can prove the remaining goals and finish the instance. *)
  Instance funext_eq_PreOrder2 A B : PreOrder (funext_eq A B) := RelInstance.
End Method2.

Section Method3.
  (* Program Instance makes this even more convenient by registering a tactic to
  run automatically. It does some of work that [RelInstance_t] is doing, so the
  tactic is written to handle Reflexive and Transitive goals in addition to
  PreOrder. *)
  Obligation Tactic := try RelInstance_t.
  Program Instance funext_eq_PreOrder3 A B : PreOrder (funext_eq A B).
End Method3.

Section Method4.
  Instance funext_eq_PreOrder A B : PreOrder (funext_eq A B) := RelInstance.
  (* here we re-use an existing instance; this particular case is not very
  useful, but if the instance is complicated and combines several existing
  instances, these kind of redundant instances like these can speed up typeclass
  resolution. *)
  Instance funext_eq_PreOrder4 : PreOrder (funext_eq nat nat).
  Proof.
    typeclasses eauto.
  Qed.
End Method4.
