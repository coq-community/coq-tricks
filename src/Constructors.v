Inductive foo :=
| bar0
| bar1
| bar2.

Ltac constructors t :=
  let make_constructors :=
      unshelve eapply exist;
      [ econstructor | match goal with
                       | |- ?x = _ => idtac x
                       end; fail ] in
  let x := constr:(ltac:(try (left; make_constructors);
                         right; exact tt) : {x:t | x = x} + unit) in
  idtac.

Goal True.
  constructors foo.
  (* bar0
     bar1
     bar2 *)
Abort.

Definition ctornum f :=
  match f with
  | bar0 => 1
  | bar1 => 2
  | bar2 => 3
  end.

Goal { f:foo | ctornum f = 3 }.
  unshelve eapply exist; [ econstructor | match goal with
                                          | |- ?g => idtac g
                                          end; reflexivity ].
Qed.
