Module Nats.
  Record natf :=
    { func : nat -> nat -> nat }.

  Definition addf :=
    {| func x y := x + y |}.
End Nats.

Module TypeAnnotation.
  Record anyf A B :=
    { func : A -> A -> B }.

  Definition first A :=
    {| func (x:A) y := x |}.
End TypeAnnotation.
