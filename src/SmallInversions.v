Goal forall T (x y : T), Some x = Some y -> x = y.
Proof.
  intros T x y H.
  refine match H with eq_refl => eq_refl end.
Qed.

Goal true <> false.
Proof.
  refine (fun H => match H with end).
  (* You could also write [refine (fun H => match H with eq_refl => I end).] *)
Qed.

Goal forall P, true = false -> P.
Proof.
  refine (fun P H => match H with end).
Qed.

Local Set Boolean Equality Schemes.
Inductive foo := a | b | c | d.

Definition foo_dec_bl x y : foo_beq x y = true -> x = y
  := match x, y with
     | a, a
     | b, b
     | c, c
     | d, d
       => fun _ => eq_refl
     | _, _ => fun H : false = true => match H with end
     end.
