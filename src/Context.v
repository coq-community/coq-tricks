Theorem test x : 1 + x = x + 2.
Proof.
  match goal with
  | [ |- ?P x = ?Q ] =>
    match Q with
    (* this context is a context pattern; it binds a context [E] with a "hole"
       where x goes (note that [x] was bound by the above pattern) *)
    | context E [x] =>
      (* this context is a function that substitutes into a context, namely
      substituting [y] into the hole in the context E *)
      let f := constr:(fun y => ltac:(let t := context E [y] in
                                   exact t)) in
      (* f is now [fun y => y + 2], the result of taking x + 2, creating the
         context _ + 2, then substituting the context under a new binder *)
      change (P x = f x)
    end
  end.
  (* goal becomes
  [1 + x = (fun y : nat => y + 2) x]
   *)
Abort.
