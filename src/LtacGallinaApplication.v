(* see https://coq.discourse.group/t/gallina-function-application-in-ltac/316
for the original question and answer *)

Notation "'subst!' y 'for' x 'in' f" := (match y with x => f end) (at level 10).

Ltac app_beta f x :=
  match f with
  | (fun y => ?F) => constr:(subst! x for y in F)
  end.

Goal True.
  match constr:(let x := 3 in x + 2) with
    (* using app_beta on f, which is bound to a function of x *)
  | let x : nat := ?y in @?f x =>
    let body_at_0 := app_beta f 0 in
    pose proof (eq_refl : body_at_0 = 0 + 2)
  end.

  (* using subst! directly on f, where x is a free variable *)
  match constr:(let x := 3 in x + 2) with
  | let x : nat := ?y in ?f =>
    let body_at_0 := constr:(subst! 0 for x in f) in
    pose proof (eq_refl : body_at_0 = 0 + 2)
  end.
Abort.
