# Constructive Analysis of First-Order Completeness

This repository contains the source code of the formalization produced alongside
the Bachelor's thesis ["A Constructive Analysis of First-Order Completeness
Theorems in Coq"][1]. A browsable version of the CoqDoc generated for these files
can be found [here][2].

## Building

The formalization has been developed and tested with the following opam packages
- `coq-8.8.2`
- `equations-1.2~beta+8.8`

The following steps will compile the source code and generate the corresponding
CoqDoc.
```
git clone https://github.com/uds-psl/fol-completeness-theorems
cd fol-completeness-theorems/coq
make
```

## Acknowledgements
The files `coq/Syntax.v` as well as `coq/FullSyntax.v` were generated
using the [AutoSubst 2][3] tool. Their dependencies `coq/axioms.v` as well as
`coq/unscoped.v` were adopted from the AutoSubst 2 source code in a slightly
modified manner.

The files `coq/Prelim.v` and `coq/DecidableEnumerable.v` were taken from the
formalization accompanying ["The files `coq/Prelim.v` and
`coq/DecidableEnumerable.v` were taken from the formalization accompanying ["On Synthetic Undecidability in Coq, with an Application to the Entscheidungsproblem"][4].
The files `coq/FOL.v`, `coq/ND.v`, `coq/Tarski.v` and `coq/Kripke.v` are based on
the files `FOL.v`, `Deduction.v`, `Semantics.v` and `Kripke.v` from that formalization,
respectively.

The files in `coq/extra` stem from [coqdocjs][5].

[1]: https://www.ps.uni-saarland.de/~wehr/bachelor.php
[2]: https://www.ps.uni-saarland.de/~wehr/bachelor/coq/toc.html
[3]: https://www.ps.uni-saarland.de/extras/autosubst2/
[4]: https://www.ps.uni-saarland.de/extras/fol-undec/
[5]: https://github.com/tebbi/coqdocjs
