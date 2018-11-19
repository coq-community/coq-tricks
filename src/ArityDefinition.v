Definition Relation T := T -> T -> Prop.
Inductive nateq : Relation nat := | equal_refl : forall n, nateq n n.
