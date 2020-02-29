(* see comment on answer https://stackoverflow.com/a/53549978/4084567 *)

Section Example.
  Context (A:Type).
  Parameter P Q: A -> Prop.
  Definition filter {a} : P a -> A := fun Pa => a.

  Lemma my_lemma:
    forall a b, Q b -> (Q b -> P a) ->
           exists a (H: P a), P (filter H).
  Proof.
    intros ?? H H0.
    do 2 eexists.
    unshelve instantiate (1 := _).
    eauto.
    auto.
  Qed.
End Example.
