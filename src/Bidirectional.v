Require Import List.
Import ListNotations.

Record vtype := { sz: nat; ty: {l: list Type | length l = sz}  }.
Definition ft (vt: vtype) := hd Type (proj1_sig vt.(ty)) -> hd Type (proj1_sig vt.(ty)).
Record func (t: vtype): Type :=
  mkFunc { f: ft t }.

(* this bidirectionality hint tells Coq to infer the type of mkFunc from its
environment without typing any of its supplied arguments. *)
Arguments mkFunc &.

Definition f1: func {| ty:= (exist _ [nat:Type] eq_refl) |} :=
  {| f := fun n => n + 1 |}.
