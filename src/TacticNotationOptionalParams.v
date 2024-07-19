(** Defining Tactic Notations to take optional parameters is somewhat annoying
currently, as it cannot be done directly with a single command. For example,
Coq's own Classes/SetoidTactics.v defines a "setoid_replace" tactic that
can take any subset of 4 optional parameters. This requires 16 distinct
Tactic Notation commands.

This can be done in a more flexible matter, using Ltac2 and a trick that
defines the parameters themselves as tactics. It takes some setting up,
so is not necessarily more concise, but it should at least be easier
to add an additional optional parameter. We will reimplement the 
"setoid_replace" Tactic Notation to illustrate.

In short, the idea is as follows:
- Define one Tactic Notation to take a tactic_list (from which we will
  extract the proper parameters)
- Define separate Ltac/Tactic Notations for each of your parameters. These will
  always throw a special Ltac2 exception that contains the true parameter.
- The outer Tactic Notation will run each of the provided parameter-tactics and
  catch their exceptions, using them appropriately.*)

Set Warnings "-undo-batch-mode".

From Coq Require Import SetoidTactics.
From Ltac2 Require Import Ltac2 Printf.
(** Next command resets the default tactic language to Ltac.*)
Set Default Proof Mode "Classic".

(** We start with defining the type of valid parameters for "setoid_replace" *)
Ltac2 Type setoid_replace_param := [
  InClause(Ltac1.t)
| AtClause(Ltac1.t)
| ByClause(Ltac1.t)
| UsingClause(Ltac1.t)
].

(** Now we extend Ltac2's exception type with a constructor designated for
passing on options to "setoid_replace"*)
Ltac2 Type exn ::= [ SetoidReplaceParamExn(setoid_replace_param) ].

(** Given an option, we can throw the corresponding exception *)
Ltac2 throw_setoid_replace_param (p : setoid_replace_param) : unit :=
  Control.zero (SetoidReplaceParamExn p).

(** To see this in action: *)
Goal True.
Fail ltac2:(throw_setoid_replace_param (InClause ltac1val:(idtac))).
Abort.

(** Now let us define Tactic Notations for each of the parameters,
starting with "at" *)

Tactic Notation "at" int_or_var_list(o) :=
(** Parsing rules force us to first write the ltac2 closure*)
  let f := ltac2:(o' |-
(** Note that ps has type [Ltac1.t], the type of Ltac1 expressions.
There are ways to manipulate these in Ltac2 (like folding over a list,
or matching on optionals) that cannot be done in Ltac1. This can
sometimes be quite useful, and we will make use of that later. *)
    throw_setoid_replace_param (AtClause o')
  ) in
  f o.

(** We proceed similarly for "in", "by" and "using" *)

Tactic Notation "in" hyp(id) :=
  let f := ltac2:(id' |-
    throw_setoid_replace_param (InClause id')
  ) in
  f id.

(** (Note using by as a parameter-tactic will probably cause conflicts with
existing definitions of "by" in actual developments. This is just an example) *)
Tactic Notation "by" tactic3(t) :=
  let f := ltac2:(t' |-
    throw_setoid_replace_param (ByClause t')
  ) in
  f t.

Tactic Notation "using" "relation" constr(rel) :=
  let f := ltac2:(rel' |-
    throw_setoid_replace_param (UsingClause rel')
  ) in
  f rel.

Ltac2 Type exn ::= [WrappedExn(message option, exn)].
(** We now need a way to 'catch' these parameters, given a runnable
'thunk' that should always throw an appropriate parameter. If it doesn't,
we will raise an error. *)
Ltac2 catch_setoid_replace_param (thunk : unit -> 'a) : setoid_replace_param :=
  match Control.case thunk with
  | Val _ => 
    let msg := fprintf "No exn was thrown, so the provided parameter is invalid"
(** Note that Control.throw throws an uncatchable exn, ie an error. *)
    in Control.throw (Invalid_argument (Some msg))
  | Err e =>
    match e with
    | SetoidReplaceParamExn p => p
    | _ =>
      let msg := fprintf "Bad exn was thrown, so the provided parameter is invalid"
      in Control.throw (WrappedExn (Some msg) e)
    end
  end.


(** We now define an Ltac2 wrapper around the four lower level Ltac
"setoidreplace" tactics. This is only necessary in this case, since the 
implementation of "setoidreplace" builds on "setoid_rewrite", 
whose [in] and [at] parameters are not very flexible. *)

Ltac2 run_setoid_replace
(** The "in" and "at" parameters, which we use to choose the appropriate variant
of "setoidreplace" *)
  (mp_in : Ltac1.t option)
  (mp_at : Ltac1.t option)

(** The "by" and "rel" parameters, for which we have a default value.
"rel" is calculated from the "using" parameter. *)
  (p_by : Ltac1.t)
  (p_rel : Ltac1.t) : unit :=
  match mp_in with
  | None =>
    match mp_at with 
    | None =>
      ltac1:(H t |- setoidreplace H t) p_rel p_by
    | Some p_at =>
      ltac1:(H t occs |- setoidreplaceat H t occs) p_rel p_by p_at
    end
  | Some p_in =>
    match mp_at with 
    | None =>
      ltac1:(H H' t |- setoidreplacein H H' t) p_rel p_in p_by
    | Some p_at =>
      ltac1:(H H' t occs |- setoidreplaceinat H H' t occs) p_rel p_in p_by p_at
    end
  end.


(** We now have everything in place to define the outer Tactic Notation. *)
Tactic Notation "setoid_replace_improved" constr(x) "with" constr(y) tactic1_list(ps) :=
  let f := ltac2:(x_raw y_raw ps_raw |-
(** Start by turning the provided [x_raw : Ltac1.t] into an [x' : constr],
the Ltac2 type of Coq terms. Same for [y_raw]. *)
    let x' := Option.get (Ltac1.to_constr x_raw) in
    let y' := Option.get (Ltac1.to_constr y_raw) in
(** We set up mutable references to store the final parameter values.
(This can be done without mutable state.) *)
    let r_mp_in := { contents := None } in
    let r_mp_at := { contents := None } in
(** Default by clause: do nothing, ie run [idtac]*)
    let r_p_by := { contents := ltac1val:(idtac) } in
(** Default using clause: use the [default_relation] *)
    let r_p_rel := { contents := constr:(default_relation $x' $y') } in
(** Now we first turn the raw tactic list [ps_raw : Ltac1.t] into an Ltac2 [list] of Ltac1 tactics *)
    let ps' : Ltac1.t list := Option.get (Ltac1.to_list ps_raw) in
(** We iterate over this list, *)
    List.iter (fun p =>
(** catch the contained parameter, *)
      let param := catch_setoid_replace_param (fun () => Ltac1.run p) in
(** and set our parameter references appropriately *)
      match param with
      | InClause i => r_mp_in.(contents) := Some i
      | AtClause a => r_mp_at.(contents) := Some a
      | ByClause t => r_p_by.(contents) := t
      | UsingClause r_raw => 
        let r := Option.get (Ltac1.to_constr r_raw) in
(** We use [x'] and [y'] here to construct the term to rewrite with *)
        r_p_rel.(contents) := constr:($r $x' $y')
      end
    ) ps';
(** Finally, we read out our parameters and pass them to [run_setoid_replace] *)
    run_setoid_replace (r_mp_in.(contents)) (r_mp_at.(contents)) (r_p_by.(contents)) (Ltac1.of_constr (r_p_rel.(contents)))
  ) in
  f x y ps.

(** Now let's see this in action. *)

Require Import Setoid.

Section test.
Context (A : Set).
Context (eqA : relation A).
Context `{!Equivalence eqA}.

Context (g : A -> A).
Context (P : A -> A -> Prop).
Context (H_P_proper : Morphisms.Proper (eqA ==> eqA ==> iff) P).

Lemma test_replace : forall a, P (g a) (g a) -> P (g a) (g a).
Proof.
intros a H.

(* no options *)
setoid_replace_improved (g a) with (g (g a)). Undo 1.

(* all 15 other options *)
setoid_replace_improved (g a) with (g (g a))
  in H. Undo 1.
setoid_replace_improved (g a) with (g (g a))
  at 1. Undo 1.
setoid_replace_improved (g a) with (g (g a))
  in H at 1. Undo 1.
setoid_replace_improved (g a) with (g (g a))
  by exfalso. Undo 1.
setoid_replace_improved (g a) with (g (g a))
  in H by exfalso. Undo 1.
setoid_replace_improved (g a) with (g (g a))
  at 1 by exfalso. Undo 1.
setoid_replace_improved (g a) with (g (g a))
  in H at 1 by exfalso. Undo 1.
setoid_replace_improved (g a) with (g (g a))
  using relation (@eq A). Undo 1.
setoid_replace_improved (g a) with (g (g a))
  in H using relation (@eq A). Undo 1.
setoid_replace_improved (g a) with (g (g a))
  at 1 using relation (@eq A). Undo 1.
setoid_replace_improved (g a) with (g (g a))
  in H at 1 using relation (@eq A). Undo 1.
setoid_replace_improved (g a) with (g (g a))
  by exfalso using relation (@eq A). Undo 1.
setoid_replace_improved (g a) with (g (g a))
  in H by exfalso using relation (@eq A). Undo 1.
setoid_replace_improved (g a) with (g (g a))
  at 1 by exfalso using relation (@eq A). Undo 1.
setoid_replace_improved (g a) with (g (g a))
  in H at 1 by exfalso using relation (@eq A). Undo 1.

(* and the order does not matter! *)
setoid_replace_improved (g a) with (g (g a))
  using relation (@eq A) by exfalso at 1 in H. Undo 1.

(* one interesting thing with the way we have currently defined it,
  is that you can provide multiply provide the same parameters.
  Currently, the last one overrides earlier ones, but it is possible to handle this differently *)
setoid_replace_improved (g a) with (g (g a)) at 1 at 2. (* replaces 2, not 1 *) Undo 1.

(* passing in unappropriate parameters will cause an error *)
Fail setoid_replace_improved (g a) with (g (g a)) at 1 idtac.
Fail setoid_replace_improved (g a) with (g (g a)) at 1 in nonexistent.

(* Prefixing parameters with tactics is actually allowed*)
setoid_replace_improved (g a) with (g (g a)) (idtac "hello!"; at 1). Undo 1.

(* using the parameters directly also gives an error.
  (One way to improve the readability of this error is to make the constructors of the 
  [setoid_replace_param] type take an additional string argument, which you set to a
  readable error message. *)
Fail at 1.

(* You can prevent direct usage of parameter-providing tactics by having their names start
  with a dash/hyphen: *)
Tactic Notation "-change_at" int_or_var_list(o) := 
  let f := ltac2:(o' |-
    throw_setoid_replace_param (AtClause o')
  ) in
  f o.
(* this prevents users from writing down:

-change_at 1. 

directly (try it: it conflicts with structuring proofs into lists of bullet points).
Users can, however, still do: *)
Fail idtac; -change_at 1.
Abort.
End test.



