# gibbon-type-safety

- [Syntax.agda](src/Syntax.agda) specifies the grammar and other details about the source langugage.

- [Typecheck.agda](src/Typecheck.agda) implements the Gibbon typechecker. There is a `tcProg` function which acts as
  the identity function when the program typechecks. Otherwise, it reports the error using a special `ErrorTy`.
  [`tcExp`](src/Typecheck.agda#L129) is where most of the action is.

- [TypeFamily.agda](src/TypeFamily.agda) has the type family (i.e Agda data types) version of the typechecker.
  We specify that something typechecks as a proposition and only valid propositions are inhabited.
  However, it cannot typecheck the complete source language at the moment.
  Namely, it lacks support for typechecking function applications (`AppE`) and pattern matches (`CaseE`).
  Also, I chose to leave out certain expressions like conditionals and tuples because they are not
  directly related to the main theme of the compiler i.e serializing values in a buffer.
  So, all we can do right now is typecheck expressions like `(Node (Leaf 1) (Leaf 2))`.
  Note that I've taken another shortcut by adding special forms to work on the "Tree" datatype.
  The `LeafE` and `NodeE` forms are special instances of the more general data constructor `DataConE` form.
  I did this to simplify the typesystem a bit and to automatically discharge certain proof obligations.

  ```Agda
  LeafE : LocVar -> Region -> Exp -> Exp
  NodeE : LocVar -> Region -> Exp -> Exp -> Exp
  ```

## Type system

The typesystem in it's current form can check if the data constructors are annotated
with correct location and region variables.
To do this, it tracks and looks for certain "constraints".
Each location arithmetic expression (i.e LocExp) has a corresponding
constraint that is added to the environment while typechecking that expression.
Later, while typechecking the data constructors, these constraints enable us to
check that the locations line up properly.

This typesystem isn't as strict as it could be, and there are many more
checks and balances that could be added.
For example, while returning a packed value via a variable, we might want to check that
there is some value written at that location.
Or we can add checks to ensure that every location is written to only once, etc.
But this typesystem doesn't implement those.

## Reduction relation

The reduction relation is relatively straighforward.
Regions are represented as [`stores`](src/TypeFamily.agda#L129)
which are just lists in Agda.
Each store value can either be a tag (like L or N etc.) or an integer.
And data constructors write values to these stores.
The locations are referred to as "cursors" and are just offsets into a store.
For example, `(Node (Leaf 1) (Leaf 2))` is represented as:


```StV ((0 , N) ∷  (1 , L) ∷ (2 , I 1) ∷ (3 , L) ∷ (4 , I 2) ∷ [])```
