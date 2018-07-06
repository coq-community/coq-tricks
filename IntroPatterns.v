Require Import Coq.Lists.List.

Section IntroPatterns.
  Variables (A : Type) (xs ys : list A).

  Example ThreeIntroPatternsCombined :
    S (length ys) = 1 -> xs ++ ys = xs.
  Proof. intros [=->%length_zero_iff_nil]. apply app_nil_r. Qed.
  (** Notes:
      [=] uses injectivity of constructors to strip of [S]s
      [intros [=H%length_zero_iff_nil].] would strip of [S]s, turn
      [length ys = 0] into [ys = nil] and move it into the context as [H]
      But [->] lets us rewrite the equation right away *)

  Theorem conditional_2 (P Q : Prop) : (P -> Q) -> ~(P /\ ~Q).
  Proof. intros p_to_q [q%p_to_q []]; exact q. Qed.
  (** Notes: %p_to_q weakens P to Q on the fly and
             [] applies the hypothesis of type (~ Q) to the goal *)

End IntroPatterns.
