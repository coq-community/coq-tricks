(* example thanks to Jonathan Leivent, Dec 2, 2016 email to coq-club

(subject Re: [Coq-Club] Unification Bug?)

https://sympa.inria.fr/sympa/arc/coq-club/2016-12/msg00007.html

 *)
Definition foo A B : (A -> B) = (A -> B) := eq_refl.

Goal { T:Type | T=T }.
   refine (exist _ (forall (x:?[T1]), ?[T2]) _).
   instantiate (T2:=ltac:(clear x)). (*remove dependency of ?T2 on x*)
   apply foo.

   Unshelve.
   all: exact nat.
Qed.
