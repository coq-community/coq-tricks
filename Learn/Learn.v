(* Forward chaining of applications, to facilitate "saturating" the known facts
without specializing. See Clément's thesis
http://pit-claudel.fr/clement/MSc/#org036d20e for a nicer explanation. *)
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
