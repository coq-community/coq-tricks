(* example thanks to Jonathan Leivent, Dec 2, 2016 email to coq-club

(subject Re: [Coq-Club] Unification Bug?")

 *)
Definition foo A B : (A -> B) = (A -> B) := eq_refl.

Goal { T:Type | T=T }.
   refine (exist _ (forall (x:?[T1]), ?[T2]) _).
   instantiate (T2:=ltac:(clear x)). (*remove dependency of ?T2 on x*)
   apply foo.

   Grab Existential Variables.
   all: exact nat.
Qed.