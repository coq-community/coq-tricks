(* Generalizable variables have a surprising effect on instances: the type of an
instance gets all free variables generalized, even without a backtick. The
coq-std++ authors (Robbert Krebbers et al) consider this a bug, and I agree. At
the very least generalizing variables in instances should be optional. *)
Class Trivial (A:Type) := trivial : unit.

(* this behavior has been fixed in Coq 8.13; this flag enables the old
surprising behavior *)
Set Instance Generalized Output.

Generalizable Variable A.
Instance generic_trivial : Trivial A.
intros A. (* instance quantifies over A *)
exact tt.
Qed.
