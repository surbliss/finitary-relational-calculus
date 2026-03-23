# Finitary Relational Calculus
Haskell-implementation of _Finitary Relational Calculus_, as described in [Henglein, Mathiesen & Rehof (2025)](https://researchprofiles.ku.dk/en/publications/finitary-relational-calculus/).

The repo consists of 3 different subprojects:
- `Generic`: a purely syntactical rewrite-system for finitary relational algebra.
- `Set`: uses the rewrite rules from Generic, with eager evaluation of 1-dimensional set operations.
- `Dict` (the main subproject): models relations as symmetric differences using a wildcard operator, enabling efficient complements and worst-case optimal intersections.

`Set` and `Dict` export smart-constructors through `Set.Term` and `Dict.Term` respectively, ensuring internal invariants are maintained, and that the `error` calls in the code are impossible to reach.

## Installing dependencies
This project uses https://github.com/srid/haskell-flake for maintaining packages.
If nix is installed, with flakes enabled, the dependencies and correct version of Haskell can be temporarily installed with
```
nix develop
```
Otherwise, use the provided cabal-file.

## Testing code
For running the tests for the `Dict.Algebra` use `cabal test`.
This includes property-based testing with QuickCheck, using a custom generator and shrinking.

## REPL usage
Load the `Dict.Term` module in repl, and use `finite`/`cofinite` to construct 1-dimensional relations.
More complicated relations can be built using the operators `\/, /\, ><` and `<+>`, alongside the constant relations `empty` and `univ`.
To show a readable representation of relations, use the `pprint` or `pshow` method.

Example usage:
```haskell
λ> :l Dict.Term
λ> x = cofinite [1,2,3] >< finite [10, 20]
λ> pprint x
{1 -> {10, 20}, 2 -> {10, 20}, 3 -> {10, 20}, * -> {10, 20}}
λ> pprint $ neg x
{1 -> {10, 20}, 2 -> {10, 20}, 3 -> {10, 20}, * -> {10, 20, *}}
λ> pprint $ neg $ neg x
{1 -> {10, 20}, 2 -> {10, 20}, 3 -> {10, 20}, * -> {10, 20}}
```
