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

Repository layout
-----------------

- `src/nbe` — the unindexed NbE development described above.
- `src/Predom*.v`, `src/domoprs.v` — the domain-theory substrate used by
  `nbe/Domains.v` and `nbe/DomainStuff.v`.
- `src/typed*.v` — the simply typed lambda-calculus formalization of
  Benton–Birkedal–Kennedy–Varming, kept as an independent historical library.
- `src/unii*.v` — the untyped lambda-calculus formalization, likewise
  independent.
- The remaining unbuilt `KS*`, `mm*` and auxiliary files are legacy material
  kept for reference and are not part of the default build.
