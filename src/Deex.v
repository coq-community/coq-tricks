Ltac deex :=
  repeat match goal with
         | [ H: exists (name:_), _ |- _ ] =>
           let name' := fresh name in
           destruct H as [name' H]
         end.

Theorem example (n:nat) (Hex: exists n, n > 3) : exists n, n > 3.
Proof.
  deex.
  (* creates a fresh n0 for the witness, and preserves the hypothesis name. *)
  exists n0; assumption.
Qed.
