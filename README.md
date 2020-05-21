# Tricks in Coq

[![Build Status](https://travis-ci.org/tchajed/coq-tricks.svg?branch=master)](https://travis-ci.org/tchajed/coq-tricks)

Some tips, tricks, and features in Coq that are hard to discover.

If you have a trick you've found useful feel free to submit an issue or pull request!

## Ltac

- The `pattern` tactic generalizes an expression over a variable. For example, `pattern y` transforms a goal of `P x y z` into `(fun y => P x y z) y`. An especially useful way to use this is to pattern match on `eval pattern y in constr:(P x y z)` to extract just the function.
- `lazymatch` is like `match` but without backtracking on failures inside the match action. If you're not using failures for backtracking (this is often the case), then `lazymatch` gets better error messages because an error inside the action becomes the overall error message rather than the uninformative "no match" error message. (The semantics of `match` mean Coq can't do obviously do better - it can't distinguish between a bug in the action and intentionally using the failure to prevent pattern matching.)
- `deex` (see [Deex.v](src/Deex.v)) is a useful tactic for extracting the witness from an `exists` hypothesis while preserving the name of the witness and hypothesis.
- `Ltac t ::= foo.` re-defines the tactic `t` to `foo`. This changes the _binding_, so tactics that refer to `t` will use the new definition. You can use this for a form of extensibility: write `Ltac hook := fail` and then use
  ```
  repeat match goal with
         | (* initial cases *)
         | _ => hook
         | (* other cases *)
         end
  ```
  in your tactic. Now the user can insert an extra case in your tactic's core loop by overriding `hook`.
- `learn` approach - see [Learn.v](src/Learn.v) for a self-contained example or [Clément's thesis](http://pit-claudel.fr/clement/MSc/#org036d20e) for more details
- `unshelve` tactical, especially useful with an eapply - good example use case is constructing an object by refinement where the obligations end up being your proofs with the values as evars, when you wanted to construct the values by proof
- `unfold "+"` works
- `destruct matches` tactic; see [coq-tactical's SimplMatch.v](https://github.com/tchajed/coq-tactical/blob/master/src/SimplMatch.v)
- using `instantiate` to modify evar environment (thanks to Jonathan Leivent on coq-club)
- `eexists ?[x]` lets one name an existential variable to be able to refer to it later
- strong induction is in the standard library: `Require Import Arith.` and use `induction n as [n IHn] using lt_wf_ind.`
- induction on the length of a list: `Require Import Coq.Arith.Wf_nat.` and `induction xs as [xs IHxs] using (induction_ltof1 _ (@length _)); unfold ltof in IHxs.`
- `debug auto`, `debug eauto`, and `debug trivial` give traces, including failed invocations. `info_auto`, `info_eauto`, and `info_trivial` are less verbose ways to debug which only report what the resulting proof includes
- `constructor` and `econstructor` backtrack over the constructors over an inductive, which lets you do fun things exploring the constructors of an inductive type. See [Constructors.v](src/Constructors.v) for some demonstrations.
- There's a way to destruct and maintain an equality: `destruct_with_eqn x`.
  You can also do `destruct x eqn:H` to explicitly name the equality
  hypothesis. This is similar to `case_eq x; intros`; I'm not sure what the
  practical differences are.
- `rew H in t` notation to use `eq_rect` for a (safe) "type cast". Need to
  import `EqNotations` - see [RewNotation.v](src/RewNotation.v) for a working
  example.
- `intro`-patterns can be combined in a non-trivial way: `intros [=->%lemma]` -- see [IntroPatterns.v](src/IntroPatterns.v).
- `change` tactic supports patterns (`?var`): e.g. `repeat change (fun x => ?f x) with f` would eta-reduce all the functions (of arbitrary arity) in the goal.
- One way to implement a tactic that sleeps for n seconds is in [Sleep.v](src/Sleep.v).
- Some tactics take an "[occurrence clause](https://coq.inria.fr/refman/proof-engine/tactics.html#occurrences-sets-and-occurrences-clauses)" to select where they apply. The common ones are `in *` and `in H` to apply everywhere and in a specific hypotheses, but there are actually a bunch of forms, for example:
  - `in H1, H2` (just `H1` and `H2`)
  - `in H1, H2 |- *` (`H1`, `H2`, and the goal)
  - `in * |-` (just hypotheses)
  - `in |-` (nowhere)
  - `in |- *` (just the goal, same as leaving the whole thing off)
  - `in * |- *` (everywhere, same as `in *`)
    These forms would be especially useful if occurrence clauses were first-class objects; that is, if tactics could take and pass occurrence clauses. Currently user-defined tactics support occurrence clauses via a set of tactic notations.
- You can use notations to shorten repetitive Ltac patterns (much like Haskell's [PatternSynonyms](https://ghc.haskell.org/trac/ghc/wiki/PatternSynonyms#Motivatingexample)). Define a notation with holes (underscores) and use it in an Ltac match, eg `Notation anyplus := (_ + _).` and then
  ```
  match goal with
  | |- context[anyplus] => idtac
  end
  ```
  I would recommend using `Local Notation` so the notation isn't available outside the current file.
- You can make all constructors of an inductive hints with `Hint Constructors`; you can also do this locally in a proof with `eauto using t` where `t` is the name of the inductive.
- The `intuition` tactic has some unexpected behaviors. It takes a tactic to run on each goal, which is `auto with *` by default, using hints from _all hint databases_. `intuition idtac` or `intuition eauto` are both much safer. When using these, note that `intuition eauto; simpl` is parsed as `intuition (eauto; simpl)`, which is unlikely to be what you want; you'll need to instead write `(intuition eauto); simpl`.
- The `Coq.Program.Tactics` library has a number of useful tactics and tactic helpers. Some gems that I like: `add_hypothesis` is like `pose proof` but fails if the fact is already in the context (a lightweight version of the `learn` approach); `destruct_one_ex` implements the tricky code to eliminate an `exists` while retaining names (it's a better version of our `deex`); `on_application` matches any application of `f` by simply handling a large number of arities.
- You can structure your proofs using bullets. You [should use them in the order](https://coq.inria.fr/refman/proof-engine/proof-handling.html#bullets) `-`, `+`, `*` so that Proof General indents them correctly. If you need more bullets you can keep going with `--`, `++`, `**` (although you should rarely need more then three levels of bullets in one proof).
- You can use the `set` tactic to create shorthand names for expressions. These are special `let`-bound variables and show up in the hypotheses as `v := def`. To "unfold" these definitions you can do `subst v` (note the explicit name is required, `subst` will not do this by default). This is a good way to make large goals readable, perhaps while figuring out what lemma to extract. It can also be useful if you need to refer these expressions.
- When you write a function in proof mode (useful when dependent types are involved), you probably want to end the proof with `Defined` instead of `Qed`. The difference is that `Qed` makes the proof term opaque and prevents reduction, while `Defined` will simplify correctly. If you mix computational parts and proof parts (eg, functions which produce sigma types) then you may want to separate the proof into a lemma so that it doesn't get unfolded into a large proof term.
- To make an evar an explicit goal, you can use this trick: `unshelve (instantiate (1:=_))`. The way this work is to instantiate the evar with a fresh evar (created due to the `_`) and then unshelve that evar, making it an explicit goal. See [UnshelveInstantiate.v](src/UnshelveInstantiate.v) for a working example.
- The `enough` tactic behaves like `assert` but puts the goal for the stated fact after the current goal rather than before.
- You can use `context E [x]` to bind a context variable, and then `let e := eval context E [y] in ...` to substitute back into the context. See
  [Context.v](src/Context.v) for an example.
- If you have a second-order match (using `@?z x`, which bind `z` to a function) and you want to apply the function, there's a trick involving a seemingly useless match. See [LtacGallinaApplication.v](src/LtacGallinaApplication.v) for an example.
- `auto with foo nocore` with the pseudo-database `nocore` disables the default `core` hint databases and only uses hints from `foo` (and the context).
- If you need to apply a theorem to a hypothesis and then immediately destruct the result, there's a concise way to do it without repetition: `apply thm in H as [x H]`, for example, might be used then `thm` produces an existential for a variable named `x`.
- If you have a hypothesis `H: a = b` and need `f a = f b`, you can use `apply (f_equal f) in H`. (Strictly speaking this is just using the `f_equal` theorem in the standard library, but it's also very much like the inverse direction for the `f_equal` tactic.)

## Gallina

- tactics in terms, eg `ltac:(eauto)` can provide a proof argument
- maximally inserted implicit arguments are implicit even when for identifier alone (eg, `nil` is defined to include the implicit list element type)
- maximally inserted arguments can be defined differently for different numbers of arguments - undocumented but [`eq_refl` provides an example](https://github.com/coq/coq/blob/trunk/theories/Init/Logic.v#L297-298)
- `r.(Field)` syntax: same as `Field r`, but convenient when `Field` is a projection function for the (record) type of `r`. If you use these, you might also want `Set Printing Projections` so Coq re-prints calls to projections with the same syntax.
- `Function` vernacular provides a more advanced way to define recursive functions, which removes the restriction of having a structurally decreasing argument; you just need to specify a well-founded relation or a decreasing measure maps to a nat, then prove all necessary obligations to show this function can terminate. See [manual](https://coq.inria.fr/refman/language/gallina-extensions.html#coq:cmd.function) and examples in `Function.v` for more details.

  Two alternatives are considerable as drop-in replacements for `Function`.

  - `Program Fixpoint` may be useful when defining a nested recursive function. See [manual](https://coq.inria.fr/refman/addendum/program.html#coq:cmd.program-fixpoint) and [this StackOverflow post](https://stackoverflow.com/questions/10292421/error-in-defining-ackermann-in-coq).
  - [CPDT's way](http://adam.chlipala.net/cpdt/html/Cpdt.GeneralRec.html) of defining general recursive functions with `Fix` combinator.

- One can pattern-match on tuples under lambdas: `Definition fst {A B} : (A * B) -> A := fun '(x,_) => x.`
- Records fields can be defined with `:>`, which make that field accessor a coercion. There are three ways to use this (since there are three types of coercion classes). See [Coercions.v](src/Coercions.v) for some concrete examples.
  - If the field is an ordinary type, the record can be used as that type (the field will implicitly be accessed). One good use case for this is whenever a record includes another record; this coercion will make the field accessors of the sub-record work for the outer record as well. (This is vaguely similar to [Go embedded structs](https://golang.org/doc/effective_go.html#embedding))
  - If the field has a function type, the record can be called.
  - If the field is a sort (eg, `Type`), then the record can be used as a type.
- When a Class field (as opposed to a record) is defined with `:>`, it becomes a hint for typeclass resolution. This is useful when a class includes a "super-class" requirement as a field. For example, `Equivalence` has fields for reflexivity, symmetry, and transitivity. The reflexivity field can be used to generically take an `Equivalence` instance and get a reflexivity instance for free.
- The type classes in RelationClasses are useful but can be repetitive to prove. [RelationInstances.v](src/RelationInstances.v) goes through a few ways of making these more convenient, and why you would want to do so (basically you can make `reflexivity`, `transitivity`, and `symmetry` more powerful).
- The types of inductives can be definitions, as long as they expand to an "arity" (a function type ending in `Prop`, `Set`, or `Type`). See [ArityDefinition.v](src/ArityDefinition.v).
- Record fields that are functions can be written in definition-style syntax with the parameters bound after the record name, eg `{| func x y := x + y; |}` (see [RecordFunction.v](src/RecordFunction.v) for a complete example).
- If you have a coercion `get_function : MyRecord >-> Funclass` you can use `Add Printing Coercion get_function` and then add a notation for `get_function` so your coercion can be parsed as function application but printed using some other syntax (and maybe you want that syntax to be `printing only`).
- You can pass implicit arguments explicitly in a keyword-argument-like style, eg `nil (A:=nat)`. Use `About` to figure out argument names.
- If you do nasty dependent pattern matches or use `inversion` on a goal and it produces equalities of `existT`'s, you may benefit from small inversions, described in this [blog post](http://gallium.inria.fr/blog/a-new-Coq-tactic-for-inversion/). While the small inversion tactic is still not available anywhere I can find, some support is built in to Coq's match return type inference; see [SmallInversions.v](src/SmallInversions.v) for examples of how to use that.
- You can use tactics-in-terms with notations to write function-like definitions that are written in Ltac. For example, you can use this facility to write macros that inspect and transform Gallina terms, producing theorem statements and optionally their proofs automatically. A simple example is given in [DefEquality.v](src/DefEquality.v) of writing a function that produces an equality for unfolding a definition.
- Notations can be dangerous since they by default have global scope and are imported by `Import`, with no way to selectively import. A pattern I now use by default to make notations controllable is to define every notation in a module with a scope; see [NotationModule.v](src/NotationModule.v).

  This pattern has several advantages:

  - notations are only loaded as needed, preventing conflicts when not using the notations
  - the notations can be brought into scope everywhere as needed with `Import` and `Local Open Scope`, restoring the convenience of a global notation
  - if notations conflict, some of them can always be scoped appropriately

- Coq has a module system, modeled after ML (eg, the one used in OCaml). You can see some simple examples of using it in [Modules.v](src/Modules.v). In user code, I've found modules to be more trouble than their worth 90% of the time - the biggest issue is that once something is in a module type, the only way to extend it is with a new module that wraps an existing module, and the only way to use the extension is to instantiate it. At the same time, you can mostly simulate module types with records.
- Coq type class resolution is extremely flexible. There's a hint database called `typeclass_instances` and typeclass resolution is essentially `eauto with typeclass_instances`. Normally you add to this database with commands like `Instance`, but you can add whatever you want to it, including `Hint Extern`s. See [coq-record-update](https://github.com/tchajed/coq-record-update) for a practical example.
- Classes are a bit special compared to any other type. First of all, in `(_ : T x1 x2)` Coq will only trigger type class resolution to fill the hole when `T` is a class. Second, classes get special implicit generalization behavior; specifically, you can write `{T}` and Coq will automatically generalize the _arguments to T_, which you don't even have to write down. See [the manual on implicit generalization](https://coq.github.io/doc/master/refman/language/gallina-extensions.html#implicit-generalization) for more details. Note that you don't have to use `Class` at declaration time to make something a class; you can do it after the fact with `Existing Class T`.

## Other Coq commands

- `Search` vernacular variants; see [Search.v](src/Search.v) for examples.
- `Search s -Learnt` for a search of local hypotheses excluding Learnt
- `Locate` can search for notation, including partial searches.
- `Optimize Heap` (undocumented) runs GC (specifically [`Gc.compact`](https://caml.inria.fr/pub/docs/manual-ocaml/libref/Gc.html))
- `Optimize Proof` (undocumented) runs several simplifications on the current proof term (see [`Proofview.compact`](https://github.com/coq/coq/blob/9a4ca53a3a021cb16de7706ec79a26e49f54de49/engine/proofview.ml#L40))
- `Generalizable Variable A` enables implicit generalization; `` Definition id `(x:A) := x `` will implicitly add a parameter `A` before `x`. `Generalizable All Variables` enables implicit generalization for any identifier. Note that this surprisingly allows generalization without a backtick in Instances; see [InstanceGeneralization.v](src/InstanceGeneralization.v). [Issue #6030](https://github.com/coq/coq/issues/6030) generously requests this behavior be documented, but it should probably require enabling some option.
- `Check` supports partial terms, printing a type along with a context of evars. A cool example is `Check (id _ _)`, where the first underscore must be a function (along with other constraints on the types involved).
- The above also works with named existentials. For example, `Check ?[x] + ?[y]` works.
- `Unset Intuition Negation Unfolding` will cause `intuition` to stop unfolding `not`.
- Definitions can be normalized (simplified/computed) easily with `Definition bar := Eval compute in foo.`
- `Set Uniform Inductive Parameters` (in Coq v8.9+beta onwards) allows you to omit the uniform parameters to an inductive in the constructors.
- `Lemma` and `Theorem` are synonymous, except that `coqdoc` will not show lemmas. Also synonymous: `Corollary`, `Remark`, and `Fact`. `Definition` is nearly synonymous, except that `Theorem x := def` is not supported (you need to use `Definition`).
- Sections are a powerful way to write a collection of definitions and lemmas that all take the same generic arguments. Here are some tricks for working with sections, which are illustrated in [Sections.v](src/Sections.v):
  - Use `Context`, which is strictly more powerful than `Variable` - you can declare multiple dependent parameters and get type inference, and can write `{A}` to make sure a parameter is implicit and maximally inserted.
  - Tactics and hints are cleared at the end of a section. This is often annoying but you can take advantage of it by writing one-off tactics like `t` that are specific to the automation of a file, and callers don't see it. Similarly with adding hints to `core` with abandon.
  - Use notations and implicit types. Say you have a section that defines lists, and you want another file with a bunch of list theorems. You can start with `Context (A:Type). Notation list := (List.list A). Implicit Types (l:list).` and then in the whole section you basically never need to write type annotations. The notation and implicit type disappears at the end of the section so no worries about leaking it. Furthermore, don't write `Theorem foo : forall l,` but instead write `Theorem foo l :`; you can often also avoid using `intros` with this trick (though be careful about doing induction and ending up with a weak induction hypothesis).
  - If you write a general-purpose tactic `t` that solves most goals in a section, it gets annoying to write `Proof. t. Qed.` every time. Instead, define `Notation magic := ltac:(t) (only parsing).` and write `Definition foo l : l = l ++ [] = magic.`. You do unfortunately have to write `Definition`; `Lemma` and `Theorem` do not support `:=` definitions. You don't have to call it `magic` but of course it's more fun that way. Note that this isn't the best plan because you end up with transparent proofs, which isn't great; ideally Coq would just support `Theorem foo :=` syntax for opaque proofs.
- Haskell has an operator `f $ x`, which is the same as `f x` except that its parsed differently: `f $ 1 + 1` means `f (1 + 1)`, avoiding parentheses. You can simulate this in Coq with a notation: `Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).` (from [jwiegley/coq-haskell](https://github.com/jwiegley/coq-haskell/blob/83a5db4b5741745ec9d522543d3616c308dfb542/src/Prelude.v#L15)).
- A useful convention for notations is to have them start with a word and an exclamation mark. This is borrowed from @andres-erbsen, who borrowed it from the Rust macro syntax. An example of using this convention is in [Macros.v](src/Macros.v). There are three big advantages to this approach: first, using it consistently alerts readers that a macro is being used, and second, using names makes it much easier to create many macros compared to inventing ASCII syntax, and third, starting every macro with a keyword makes them much easier to get parsing correctly.
- To declare an axiomatic instance of a typeclass, use `Declare Instance foo : TypeClass`. This better than the pattern of `Axiom` + `Existing Instance`.
- To make Ltac scripts more readable, you can use `Set Default Goal Selector "!".`, which will enforce that every Ltac command (sentence) be applied to exactly one focused goal. You achieve that by using a combination of bullets and braces. As a result, when reading a script you can always see the flow of where multiple goals are generated and solved.
- `Arguments foo _ & _` (in Coq 8.11) adds a _bidirectionality hint_ saying that an application of `foo` should infer a type from its arguments after typing the first argument. See [src/Bidirectional.v](Bidirectional.v) for an example and the [latest Coq documentation](https://coq.github.io/doc/master/refman/language/gallina-extensions.html?highlight=bidirectional#coq:cmd.arguments-bidirectionality-hints).
- Coq 8.11 introduced compiled interfaces, aka `vos` files (as far as I can tell there are a more principled replacement for `vio` files). Suppose you make a change deep down to `Lib.v` and want to start working on `Proof.v` which imports `Lib.v` through many dependencies. With `vos` files, you can recompile all the _signatures_ that `Proof.v` depends on, skippinng proofs, and keep working. The basic way to use them is to compile `Proof.required_vos`, a special dependency `coqdep` generates that will build everything needed to work on `Proof.v`. Coq natively looks for `vos` files in interactive mode, and uses empty `vos` files to indicate that the file is fully compiled in a `vo` file.

  Note that Coq also has `vok` files; it's possible to check the missing proofs in a `vos` file, but this does not produce a `vo` and so all Coq can do is record that the proofs have been checked. They can also be compiled in parallel within a single file, although I don't know how to do that. Compiling `vok`s lets you fairly confidently check proofs, but to really check everything (particularly universe constraints) you need to build `vo` files from scratch.

  Signature files have one big caveat: if Coq cannot determine the type of a theorem or the proof ends with `Defined` (and thus might be relevant to later type-checking), it has to run the proof. It does so _silently_, potentially eliminating any performance benefit. The main reason this happens is due to proofs in a section that don't annotate which section variables are used with `Proof using`. Generally this can be fixed with `Set Default Proof Using "Type"`, though only on Coq master and not on Coq 8.11.0.

- Coq 8.12+alpha has a new feature `Set Printing Parentheses` that prints parentheses as if no notations had an associativity. For example, this will print `(1,2,3)` as `((1,2),3)`. This is much more readable than entirely disabling notations.
- You can use `Export Set` to set options in a way that affects any file directly importing the file (but not transitively importing, the way `Global Set` works). This allows a project to locally set up defaults with an `options.v` file with all of its options, which every file imports. You can use this for basic sanity settings, like `Set Default Proof Using "Type".` and `Set Default Goal Selector "!"` without forcing them on all projects that import your project.

## Using Coq

- You can pass `-noinit` to `coqc` or `coqtop` to avoid loading the standard library.
- Ltac is provided as a plugin loaded by the standard library; to load it you need `Declare ML Module "ltac_plugin".` (see [NoInit.v](src/NoInit.v)).
- Numeral notations are only provided by the prelude, even if you issue `Require Import Coq.Init.Datatypes`.
- If you use Coq master, the latest Coq reference manual is built and deployed to <https://coq.github.io/doc/master/refman/index.html> automatically.
