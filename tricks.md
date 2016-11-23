Run a PACS meeting and present neat tricks

* `pattern` tactic
* `lazymatch` for better error messages
* `Search` vernacular variants
* `deex` tactic
* `::=` to re-define Ltac
* `learn` approach
* tactics in terms
  * `ltac:(eauto)` for argument to proof
* `unshelve` tactical, especially useful with an eapply - good example use case is constructing an object by refinement where the obligations end up being your proofs with the values as evars, when you wanted to construct the values by proof
* `Search s -Learnt` for a search of local hypotheses excluding Learnt
* `unfold "+"` works
* `destruct matches` tactic
