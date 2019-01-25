Notation "'Some!' x <- a ; f" :=
  (match a with
   | Some x => f
   | _ => None
   end)
    (right associativity, at level 70, x pattern).

Notation "'ret!' x" := (Some x) (at level 60).

Definition opt_map A B (x:option A) (f: A -> B) : option B :=
  Some! x <- x; ret! f x.
