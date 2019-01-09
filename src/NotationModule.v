From Coq Require Import List.

Section Array.
  Context (A:Type).
  Notation list := (list A).
  Implicit Types (l:list) (n:nat) (x:A).

  Fixpoint assign l n x' : list :=
    match l with
    | nil => nil
    | x::xs => match n with
              | 0 => x'::xs
              | S n => x::assign xs n x'
              end
    end.

  Fixpoint index l n : option A :=
    match l with
    | nil => None
    | x::xs => match n with
              | 0 => Some x
              | S n => index xs n
              end
    end.
End Array.

Module ArrayNotations.
  Declare Scope array_scope.
  Delimit Scope array_scope with array.
  Notation "l [ i  :=  v ]" := (assign l i v) (at level 10, left associativity) : array_scope.
  Notation "l [ i ]" := (index l i) (at level 11, no associativity) : array_scope.
End ArrayNotations.

(* to use ArrayNotations: *)
Import ArrayNotations.
Local Open Scope array_scope. (* optional *)
