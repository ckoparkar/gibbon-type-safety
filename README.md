# gibbon-type-safety

- [Syntax.agda](Syntax.agda) specifies the grammar and other details about the source langugage.

- [Typecheck.agda](Typecheck.agda) implements the Gibbon typechecker. There is a `tcProg` function which acts as
  the identity function when the program typechecks. Otherwise, it reports the error using a special `ErrorTy`.
  `tcExp` is where most of the action is.

- [TypeFamily.agda](TypeFamily.agda) has the type family (i.e Agda data types) version of the typechecker.
  We specify that something typechecks as a proposition and only valid propositions are inhabited.
  However, it cannot typecheck the complete source language at the moment.
  Namely, it lacks support for typechecking function applications (`AppE`) and pattern matches (`CaseE`).
  <!-- and certain features like conditionals and tuples. -->
  Also, I chose to leave out certain expressions like conditionals and tuples because they are not
  directly related to the main theme of the compiler i.e serializing values in a buffer.
  So, all we can do is typecheck expressions like "(Node (Leaf 1) (Leaf 2))". Note that I've taken another
  shortcut by adding special forms to work on the "Tree" datatype.
  The `LeafE` and `NodeE` forms are special instances of the more general data constructor `DataConE` form.
  I did this to simplify the typesystem a bit and to automatically discharge certain proof obligations.

  ```Agda
  LeafE      : LocVar -> Region -> Exp -> Exp
  NodeE      : LocVar -> Region -> Exp -> Exp -> Exp
  ```

## Type system

## Reduction relation
