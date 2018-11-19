(* coercion to nat *)
Record small_number :=
  { num :> nat;
    num_small : num < 3 }.

Check (fun (n:small_number) => n + 3).

(* coercion to Funclass *)
Record nat_set :=
  { is_member :> nat -> bool;
    max : nat;
    no_higher_members : forall n, n > max -> is_member n = false; }.

Check (fun (s:nat_set) => s 3).

(* coercion to Sortclass *)
Record magma :=
  { A :> Type;
    op : A -> A -> A;
    op_assoc : forall x y z, op x (op y z) = op (op x y) z; }.

(* note that m is not a type, but can be used as one *)
Check (fun (m:magma) (x:m) => op m x x).

(* coercions are printing by default (so the above examples are printed as
   written), but we can display the calls to the accessors explicitly *)
Set Printing Coercions.
Check (fun (m:magma) (x:m) => op m x x).
(* [fun (m : magma) (x : A m) => op m x x
     : forall m : magma, A m -> A m] *)
