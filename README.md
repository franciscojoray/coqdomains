coqdomains
==========

Domain theory and denotational semantics in Coq

Normalisation by evaluation
---------------------------

The unindexed NbE development lives under `src/nbe`:

- `Lang.v` — context-free syntax and renaming/substitution.
- `Types.v` — simple type system over the unindexed syntax.
- `Domains.v` — call-by-name recursive domain.
- `SemOps.v`, `Semantics.v` — semantic value operators and term semantics.
- `Levels.v`, `Reif.v`, `NbE.v` — level convention, readback and normalisation.
- `TypedNbE.v`, `Validity.v`, `TypedEq.v`, `Weakening.v`, `EqSubst.v`,
  `SemSubst.v` — typed semantics, validity, equality and substitution.
- `LogicalRel.v`, `Correctness.v`, `Completeness.v` — logical relations and
  the main theorems.

Build the development with:

```
make -C src
```
