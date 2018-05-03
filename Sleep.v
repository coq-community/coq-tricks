Tactic Notation "sleep" integer(seconds) :=
  do seconds try solve [ timeout 1 (repeat eapply (fun (A B : Type) (f : A -> B) (x : A) => f x)) ].
