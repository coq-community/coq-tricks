Require Import Arith.

Search "mod" "/".

Search (_ + ?a - ?a).

Search sumbool (@eq bool _ _).

Search ({_=_} + {_<>_}).

(* Note that there is another theorem if this form in ProofIrrelevance (that
works without decidable equality but requires the axiom of proof irrelevance -
the search will not find it if ProofIrrelevance has not been Require'd. *) *)
Search (existT ?P ?x _ = existT ?P ?x _).

Search list outside List.

Search plus inside List.

(* searches use the name of the theorem of the string does not resolve to a
notation *)
Search "dec" "<".
