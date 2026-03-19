# Finitary Relational Calculus
Haskell-implementation of _Finitary Relational Calculus_, as described at https://researchprofiles.ku.dk/en/publications/finitary-relational-calculus/.

The repo consists of 3 differents subprojects:
- `Generic` is a purely syntactical rewrite-system.
- `Set` uses the rewrite rules from Generic, but does set intersections and unions eagerly, when combining 1-dimensional sets
- `Dict` is a very different approach: It models relations as _symmetric differences_ using a wild-card operator, to make complements easier to produce.

A report is in progress for the contents of this repo.

## Running the code
Code can tested through the reple: Running `cabal run` and loading `Dict.Algebra`, (co)finite relations can be made with `finite`/`cofinite`, operations can be made with the `Algebra`/`Negatable` operators, and the result can be printed using `pprint` or `pshow`.

The `Dict.Algebra` module also contains QuickCheck tests, with custom generators. Run then with `cabal test`.
