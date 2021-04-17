From Coq Require Import ZArith.
From Coq Require Import Lia.

(* [lia] by default can't handle some non-linear arithmetic lia division and
modulo at all. However, we can change the pre-processing step ([zify]) to at
least make some equations about division and modulo available, which can solve
simple goals involving non-linear arithmetic. *)

(* see https://coq.github.io/doc/master/refman/addendum/micromega.html for a lot
more details on how to use [zify_post_hook] as well as extend zify in other
ways. *)

Open Scope Z.

Lemma mod_bound (n k: Z) :
  0 <= n ->
  0 < k ->
  n mod k < k.
Proof.
  intros.
  Fail lia.
Abort.

(* [lia] is now more powerful (but potentially slower) *)
Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma mod_bound (n k: Z) :
  0 <= n ->
  0 < k ->
  n mod k < k.
Proof.
  intros.
  lia.
Qed.
