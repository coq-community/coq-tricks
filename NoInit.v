(* note that this file is intended to demonstrate use of Coq's -noinit (same
as -nois) option, which does not load the standard library. Ltac is loaded by
the standard library's prelude, so with -noinit you'll need to load it
manually. *)

Declare ML Module "ltac_plugin".
Ltac foo := idtac.
