Require Import Learn.

Section LearnExample.

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