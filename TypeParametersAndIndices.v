(*** Parameters vs indices *)

(* Here we explain the difference between parameters (arguments to an inductive
before the colon) and indices (arguments after the colon) with an example. See
https://stackoverflow.com/questions/24600256/difference-between-type-parameters-and-indices
for the original example and a good explanation *)

(* Parameters make a type "generic" in the sense of polymorphism in other
languages; think lists, which can have elements of different types but look the
same regardless of what the element type is. *)
(* Indices, on the other hand, can affect what inhabitants are in the type. In
other languages inductives with indices are called GADTs. A type can behave
quite differently depending on the index it is passed, and knowing the index of
a type tells you something about its constructors. In Coq the classic example is
[Fin.t n], where [n] determines how many distinct values [Fin.t n] has. *)

(* Although you can always make everything an index and just happen to use it uniformly over the constructors, the induction principle Coq generates is much better if you make uniform indices parameters instead, as illustrated here. *)


(* we use undo intentionally so disable the warning about its efficiency *)
Set Warnings "-undo-batch-mode".

Module UsingParameter.
  Inductive F (T:Type) : nat -> Type :=
  | C1 : T -> F T 0
  | C2 : F T 1
  | C3 : F T 0.
  Arguments C1 {T} v.
  Arguments C2 {T}.
  Arguments C3 {T}.
  Check F_ind.
  (*
F_ind
     : forall (T : Type) (P : forall n : nat, F T n -> Prop),
       (forall t : T, P 0 (C1 T t)) ->
       P 1 (C2 T) ->
       P 0 (C3 T) ->
       forall (n : nat) (f2 : F T n), P n f2
   *)

  Definition getn T (x: F T 0) : nat :=
    match x with
    | C1 _ => 0
    | C3 => 3
    end.

  Definition f_unit_id n (x:F unit n) : F unit n.
    induction x.
    exact (C1 t).
    exact C2.
    exact C3.
  Defined.

  Definition f_bool_not n (x:F bool n) : F bool n :=
    match x with
    | C1 b => C1 (negb b)
    | C2 => C2
    | C3 => C3
    end.
End UsingParameter.

Module UsingUniformIndex.
  Inductive F : Type -> nat -> Type :=
  | C1 : forall T, T -> F T 0
  | C2 : forall T, F T 1
  | C3 : forall T, F T 0.
  Arguments C1 {T} v.
  Arguments C2 {T}.
  Arguments C3 {T}.
  Check F_ind.
  (*
F_ind
     : forall P : forall (T : Type) (n : nat), F T n -> Prop,
       (forall (T : Type) (t : T), P T 0 (C1 T t)) ->
       (forall T : Type, P T 1 (C2 T)) ->
       (forall T : Type, P T 0 (C3 T)) ->
       forall (T : Type) (n : nat) (f2 : F T n), P T n f2
*)
  (* note that induction over F T now has a motive that abstracts over T *)

  (* we want to invert the boolean in the C1 constructor *)
  Fail Definition f_bool_not n (x:F bool n) : F bool n :=
    match x with
    | C1 b => C1 _ (negb b)
    | C2 => C2
    | C3 => C3
    end.
  (* b has type [T] in the first branch when we knew it has type [bool] *)

  (* We can see what goes wrong using tactics (note that this is an
  approximation; pattern matches are in general compiled with a different
  implementation than the [induction] tactic. However in this case the problem
  is that there's no straightforward way to generate this proof; it requires a
  type equality since the F recursion principle must be generic over T. *)
  Definition f_bool_not n (x:F bool n) : F bool n.
    induction x.
(* we've lost any information about the bool parameter to F and
    need to do the proof generically over T - the solution was to generalize bool
    to T and keep a proof [T = bool], prove something of the form [T = bool -> ...],
    and then apply it to the proof [T = bool]. *)
    Undo.
    remember (bool:Type) as T.
    induction x; subst.
    exact (C1 (negb t)).
    exact C2.
    exact C3.
  Defined.

End UsingUniformIndex.

(* While parameters cannot vary between the type constructed by each of the
constructors, arguments to constructors can use the inductive at different
types. *)
Module VaryingParameterInArguments.
  Module Ex1.
    Inductive F (T:Type) : Type :=
    | C1 : F nat -> F T
    | C2 : T -> F T.
  End Ex1.

  Module Ex2.
    Inductive F (T:Type) : Type :=
    | C1 : (T -> F nat) -> F T
    | C2 : T -> F T.
  End Ex2.

  Module Ex3.
    Fail Inductive F (T:Type) : Type :=
    (* this is a non-positive occurrence of F, which is never allowed because
      it can be used to create proofs of False and thus breaks soundness of Coq
      as a logic *)
    | C1 : (F T -> nat) -> F T
    | C2 : T -> F T.
  End Ex3.
End VaryingParameterInArguments.
