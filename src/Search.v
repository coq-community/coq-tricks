Require Import Arith.

(* by default search components are AND'd together, so more components results
in a more specific search *)
Search plus minus.

(* searching for notations - note that this has to be a token corresponding to
exactly one notation (for more general searches, first find the right pattern
with Locate and then search for that) *)
Search "/" "+".

(* search patterns can be non-linear (within one component) *)
Search (_ + ?a - ?a).

Search sumbool (@eq bool _ _).

Search ({_=_} + {_<>_}).

(* Note that there is another theorem if this form in ProofIrrelevance (that
works without decidable equality but requires the axiom of proof irrelevance -
the search will not find it if ProofIrrelevance has not been Require'd. *)
Search (existT ?P ?x _ = existT ?P ?x _).

Search plus inside List.

(* searches use the name of the theorem if the string is an identifier *)
Search "dec" "<".

(* mod is part of a notation, but searching for ["mod"] will look for the string
in the lemma name; to search for the notation search for the keyword with
["'mod'"]. (note that Nat.testbit_eqb, for example, does not have mod in the name) *)
Search "'mod'" 2.
(* the above search would probably be better done like this: *)
Search (_ mod 2).
