Require Vector.
Import Vector.VectorNotations.

Record vtype := { sz: nat; ty: Vector.t Type (S sz) }.
Definition ft (vt: vtype) := Vector.hd vt.(ty) -> Vector.hd vt.(ty).
Record func (t: vtype): Type :=
  mkFunc { f: ft t }.

(* this bidirectionality hint tells Coq to infer the type of mkFunc from its
environment without typing any of its supplied arguments. *)
Arguments mkFunc &.

Definition f1: func {| ty:= [nat:Type] |} :=
  {| f := fun n => n + 1 |}.
