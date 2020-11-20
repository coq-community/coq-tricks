(* Here's how local, global, and export hints work in Coq.

  Very similar principles apply to definitions, but hints are a little special
  in that:
  (1) you can't name them to retrieve them locally (whereas you can qualify the
  module for an un-exported definition and still use it) and (2) it's hard to
  determine their scope because you can't name them and figure out where they
  are
*)
Module A.
  (* gfact will have a global hint proving it,
    efact will have an export hint,
    and lfact only as a local hint *)
  Axioms gfact efact lfact  : Prop.
  Axiom gfact_true : gfact.
  Axiom efact_true : efact.
  Axiom lfact_true : lfact.

  Global Hint Resolve gfact_true : core.
  #[export] Hint Resolve efact_true : core.
  Local Hint Resolve lfact_true : core.
End A.

Module B.
  Import A.
  (* here we directly imported both hints, so export vs
    global makes no difference, but we don't have the
    local one *)

  Goal A.gfact.
  Proof. auto. Qed.

  Goal A.efact.
  Proof. auto. Qed.

  Goal A.lfact.
  Proof. Fail progress auto. Abort.
End B.

Module C.
  Import B.
  (* here we only have the global hint from A, not the export one *)

  Goal A.gfact.
  Proof. auto. Qed.

  Goal A.efact.
  Proof.
    (* doesn't work, we need to import A to get the relevant
    * hint *)
    Fail progress auto.
  Abort.

  Goal A.lfact.
  Proof. Fail progress auto. Abort.
End C.
