Import EqNotations.

(* just an example context for rewriting *)
Require Fin.

Definition cast {n m: nat} (H: n = m)
           (f: Fin.t n) : Fin.t m :=
  rew H in f.

Print cast. (* prints as rew [Fin.t] H in f *)

Definition cast_is n m (H: n = m) (f: Fin.t n) :
    cast H f = eq_rect n Fin.t f m H := eq_refl.

