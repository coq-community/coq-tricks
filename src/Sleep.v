Tactic Notation "sleep" integer(seconds) :=
  do seconds try solve [ timeout 1 (repeat eapply proj1) ].

Goal True.
  sleep 3.
  exact I.
Qed.
