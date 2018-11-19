Section S.
  Variable A:Type.
  (* Variable n:nat. *)

  (* Top-level tactics are checked strictly - they must not have any undefined
  symbols. But they can access section variables! *)
  Ltac ltac_can_refer_to_section_variables :=
    match goal with
    | [ H: A |- _ ] =>
      idtac H
    end.

  (* with some tactics-in-terms trickery we can check the current (Ltac)
  environment *)

  (* this appears useless - doesn't the proof state show the same information? *)
  Ltac print_env :=
    repeat match reverse goal with
           | [ H: ?t |- _ ] =>
             idtac H ":" t; fail
           end.

  (* ...except in contexts where there is no interactive proof state *)
  Check ltac:(print_env; exact true).

  (* the same tactic applies to evar contexts: *)
  Goal True.
    evar (e1:nat).
    evar (e2:nat).
    (* e1 depends on A *)
    instantiate (e1:=ltac:(print_env)).
    (* e2 depends on A and e1 *)
    instantiate (e2:=ltac:(print_env)).
    (* Note that this trick actually instantiates the evars; because the tactic
    doesn't solve the goal, the evars are replaced by new ones, so you can't do
    this trick twice in a script (there's no way to refer to the new evar here
    because the goal doesn't contain them), but you can always revert and do
    something else. *)
  Abort.
End S.
