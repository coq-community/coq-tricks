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

Search list outside List.

Search plus inside List.

(* searches use the name of the theorem if the string is an identifier *)
Search "dec" "<".

(* mod is part of a notation, but searching for ["mod"] will look for the string
in the lemma name; to search for the notation search for the keyword with
["'mod'"]. (note that Nat.testbit_eqb, for example, does not have mod in the name) *)
Search "'mod'" 2.
(* the above search would probably be better done like this: *)
Search (_ mod 2).

(* note that requiring ssreflect in _any transitive dependency_ hijacks the
built-in Search and replaces it with ssreflect, which is similar but slightly
different.
 *)
Require ssreflect.
(* ssreflect Search has only one improvement over Coq's builtin Search and a
serious footgun.

The improvement is that searches for a notation also return the notation's
definition, so you don't need a separate [Locate].

The footgun is that the first component of an ssreflect search is special and
only matches within the "conclusion" (the tail of a sequence of [forall] and
[->]). To disable this, you need to pass a wildcard for the first position. *)

(* for example, let's try to find the function [nth_error : list A -> nat ->
option A], knowing only that we want some function to lookup in a list. *)

(* this is a pretty sensible search *)
Search list nat option.
(* ... but it returns a warning [Warning: Listing only lemmas with conclusion
matching (list _)], which is of course useless. *)

(* instead, you need to do this: *)
Search _ list nat option.
