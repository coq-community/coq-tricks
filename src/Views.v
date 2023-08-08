(** The first part of this file gives some definitions to make the case for an example of views. *)
(** The last parts of the file demonstrate why a view may be useful. *)

(** For more details, see the mathcomp book, section 5.1 on "Reflection Views" https://zenodo.org/record/7118596 *)
(** The following is another real-world example that defines a view on a list such that the list is reversed:
   https://github.com/math-comp/math-comp/blob/7d5618d936496d1f99a76abeb9c636dd3ddaf293/mathcomp/ssreflect/seq.v#L360-L364 *)
Require Import String.

Inductive expr : Type :=
| Value : nat -> expr
| Var : string -> expr
| Plus : expr -> expr -> expr
| Let : string -> expr -> expr -> expr
.
Inductive ectx : Type :=
| Ehole : ectx
| EplusR : nat -> ectx -> ectx
| EplusL : ectx -> expr -> ectx
| Elet : string -> ectx -> expr -> ectx
.
(** This function determines the evaluation context of an expression. *)
Fixpoint find_ectx (e : expr) : option(ectx * expr) :=
  match e with
  | Plus e0 e1 =>
    match e0, e1 with
    | Value n0, Value n1 => Some(Ehole, Plus (Value n0) (Value n1))
    | Value n0, _ =>
      match find_ectx e1 with
      | Some(E, e1') => Some(EplusR n0 E, e1')
      | None => None
      end
    | _, _ =>
      match find_ectx e0 with
      | Some(E, e0') => Some(EplusL E e1, e0')
      | None => None
      end
    end
  | Let x e0 e1 =>
    match e0 with
    | Value n0 => Some(Ehole, Let x (Value n0) e1)
    | _ =>
      match find_ectx e0 with
      | Some(E, e0') => Some(Elet x E e1, e0')
      | None => None
      end
    end
  | _ => None
  end
.
(** The following lemma shows when and why you'd want to use views. *)
Lemma same e e' :
  find_ectx e = Some(Ehole, e') ->
  e = e'
.
Proof.
  intros; destruct e; try (now inversion H); cbn in H.
  - (* e1 is either a value or any other expression *)
    destruct e1.
    (* this generated 4 subgoals, one of them concerned with a value,
       one spurious case, and n=2 exactly similar goals.
       n gets larger the more expressions exist and
       all these n goals have exactly the same proof *)
    (* again, e2 is either a value or any other expression, thereby we 
       get to n * n goals with exactly similar proofs *)
Abort.

(** * Views *)
(* Views allow us to focus the case analysis on just the relevant parts,
   "combining" all the similar goals to just one. *)
Inductive expr_view : expr -> Type :=
| expr_view_value : forall n, expr_view (Value n)
| expr_view_expr : forall e, (forall n, e <> Value n) -> expr_view e
.
#[local]
Hint Constructors expr_view : core.

(** The following can be used to construct a view from an arbitrary expression. *)
Lemma e_view e : expr_view e.
Proof. destruct e; try econstructor; congruence. Qed.

Lemma same e e' :
  find_ectx e = Some(Ehole, e') ->
  e = e'
.
Proof.
  intros; destruct e; try (now inversion H); cbn in H.
  - (* e1 is either a value or any other expression. By destructing the view,
       this information gets reflected now: Only two goals are generated,
       instead of four goals *)
    destruct (e_view e1).
    (* That's basically the trick. *)
Abort.
