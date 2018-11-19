(* Forward chaining of applications, to facilitate "saturating" the known facts
without specializing. See Clément's thesis
http://pit-claudel.fr/clement/MSc/#org036d20e for a nicer explanation. *)
Module Learn.
  Inductive Learnt {P:Prop} :=
  | AlreadyLearnt (H:P).

  Local Ltac learn_fact H :=
    let P := type of H in
    lazymatch goal with
    (* matching the type of H with the Learnt hypotheses means the
    learning fails even when the proposition is known by a different
    but unifiable type term *)
    | [ Hlearnt: @Learnt P |- _ ] =>
      fail 0 "already knew" P "through" Hlearnt
    | _ => pose proof H; pose proof (AlreadyLearnt H)
    end.

  Tactic Notation "learn" constr(H) := learn_fact H.
End Learn.

Section LearnExample.
  Import Learn.

  Parameter P : nat -> Prop.
  Parameter Q R : nat -> nat -> Prop.

  Axiom P_Q : forall {x}, P x -> exists y, Q x y.
  Axiom Q_R : forall {x y}, P x -> Q x y -> R y x.

  Goal forall x, P x -> exists y, R y x.
  Proof.
    repeat match goal with
           | _ => progress intros
           | [ H: _ /\ _ |- _ ] => destruct H
           | [ H: exists _, _ |- _ ] => destruct H
           | [ H: P _ |- _ ] => learn (P_Q H)
           | [ H: P ?x, H': Q ?x _ |- _ ] => learn (Q_R H H')
           | [ |- exists _, _ ] => eexists
           | _ => eassumption
           end.
  Qed.

End LearnExample.
