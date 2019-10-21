(* module types are collections of definitions and their types. These are
sometimes called "signatures" and you can think of them as "interfaces" (this
terminology as opposed to module type is more common in OCaml; Coq's module
system is modeled off of OCaml's) *)

Module Type NatM.
  Axiom number:nat.
End NatM.

(* a module can implement a module type, which means it needs to supply a
definition for all the axioms in the module type. *)
(* somewhat confusingly, module types can include definitions, in which case
modules must contain exactly equivalent definitions. *)

Module ExampleNat <: NatM.
  Definition number := 3.
End ExampleNat.

Module Type Counter.
  Axiom T:Type.
  Axiom new : T.
  Axiom add: T -> T.
  Axiom get: T -> nat.
End Counter.

(* Note that this module just says [: Counter]. This is called "opaque
ascription" and it means that the only thing callers know about this module is
that it implements Counter. In this case, Counter doesn't expose any theorems,
so callers can't reason about its implementation, but in general it would.
Nonetheless you can use this module to write code. *)
Module SimpleCounter : Counter.
  Definition T := nat.
  Definition new : T := 0.
  Definition add c := 1 + c.
  Definition get (x:T) := x.
End SimpleCounter.

(* Modules can be parameterized, taking other modules of some module type as an argument. *)
(* For unclear reasons this is called a "module functor" (there's some loose
connection to category theory). You still see that terminology in OCaml. *)
Module UseCounter (C:Counter) <: NatM.
  (* note that new need C.get because even though a counter might be represented
  as a nat (as above), the signature doesn't say anything about that. *)
  Definition number := C.get (C.add (C.add C.new)).
End UseCounter.

(* it's possible to apply a module functor (parametrized module) to concrete
modules, of the appropriate signatures. *)
Module UseSimpleCounter := UseCounter SimpleCounter.

(* Note that in Coq, with dependent types it's possible to simulate most of the
features of modules with ordinary types. Module types are like record types,
their implementations are like values of the record type, and module functors
are ordinary functions. However, modules do provide some syntactic conveniences
(you can write several definitions more easily), and modules can use opaque
ascription which is a bit "more hidden" than an ordinary opaque definition in
Coq. *)

(* Module types can also have other modules types as parameters, which we didn't
demonstrate here. *)
