(* searching for notations *)
Locate "+".

(* it's possible to search with a single token (if you don't know what the parts
of the notation are) *)
Locate "{".

(* check shows a context for any evars in its argument *)
Check (id _ _).

(* it also supports naming them, for a more readable context *)
Check (id _ ?[f]).
Check ?[x] + ?[y].
