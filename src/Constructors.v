Inductive foo :=
| bar0
| bar1
| bar2.

Definition ctornum f :=
  match f with
  | bar0 => 1
  | bar1 => 2
  | bar2 => 3
  end.

(* an illustration of constructor backtracking *)
Goal { f:foo | ctornum f = 3 }.
  unshelve eapply exist; [ constructor | match goal with
                                          | |- ?g => idtac g
                                          end; reflexivity ].
Qed.

(* same as above, but more directly *)
Definition foo_by_ctornum : {f:foo | ctornum f = 3}.
Proof.
  (* the tactic after the ; works only because [constructor] backtracks until
     [reflexivity] succeeds. *)
  unshelve refine (exist _ _ _); [ constructor | reflexivity].
Defined.

Inductive NumIsGood (n:nat) : Prop :=
| Good0 (H: n = 0)
| Good3 (H: n = 3)
| Good7 (H: n = 7)
.

Lemma three_is_good : NumIsGood 3.
Proof.
  (* [constructor] on its own would pick [Good0], resulting in an unprovable
  goal. Adding [solve [ eauto ]] means the whole tactic backtracks on the choice
  of constructor. *)
  constructor; solve [ eauto ].
Qed.

(* a fun but not very useful thing we can do with constructor backtracking is to
print them out: *)
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
  (* output:
     bar0
     bar1
     bar2 *)
Abort.
