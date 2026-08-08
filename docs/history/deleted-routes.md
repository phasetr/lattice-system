---
layout: page
title: "Deleted proof routes"
permalink: /history/deleted-routes/
---

# Deleted proof routes

> Historical record moved losslessly from the former monolithic index.

<!-- legacy-source:start:72:109 -->
### Deleted routes: what this index used to document

Three abandoned proof routes had one index row per declaration.  Their modules
were deleted, so the rows described declarations and files that no longer
exist; the 590 affected rows were removed (PR #5143, issue #5140).  What was
there, and how it went away:

| Route the rows described | Heading they sat under | Removed by |
|---|---|---|
| Later γ-4 layers: predicted ground-state subspace and minimum energy of the bipartite toy model (`bipartiteToyGroundStateSubspacePredicted*`, `bipartiteToyMinEnergyPredicted*`, `bipartiteImbalanceWeight*`), Néel-state toy-Hamiltonian expectations (`neelStateOfS*`, `heisenbergToyHamiltonianS*`) and their spin-`1/2` mirrors (`neelStateOf*`) | Total spin operator (Tasaki §2.2 eq. (2.2.7), (2.2.8)) — 540 rows | PR #3919 (`7b65d59e`, "delete 525 orphan modules, 35,002 lines"): 480 of the 482 modules those rows named; the other 2 paths are files that still exist |
| Callback-threaded `Theorem23*` chain toward `tasaki_2_5_theorem_2_3` (energy-interval chains, lowering/raising predecessor coefficients, joint cross-ladder wrappers) | Spin-`S` Marshall–Lieb–Mattis on the magnetization sector (Tasaki §2.5 Theorem 2.2 generic S, sector form) — 25 rows | PR #3645 (`f7947dfc`, "delete unsound saturated-ladder Theorem 2.3 route", 40 wrapper modules) for 8 modules; PR #3919 for the other 14 |
| Saturated ferromagnetic ladder-iterate state (`ladderIterateUp_*`, `allAlignedStateS` / `totalSpinSOp{Plus,Minus}` expectation variants, `saturatedFerromagnetJointEigenspace*`) | Spin-`S` saturated ferromagnetic state (Tasaki §2.4 generalised) — 25 rows | PR #3919, all 25 modules |

The surviving parts keep their rows: the earlier γ-4 steps (sublattice
operators, sublattice Casimir, SU(2) commutation) and the sound per-sector
Perron–Frobenius route to `tasaki_2_5_theorem_2_3`.  The globs in the table
above name **the deleted variant families, not the stems they are built on**:
every one of those stems (`bipartiteToyGroundStateSubspacePredicted`,
`bipartiteToyMinEnergyPredicted`, `bipartiteImbalanceWeight`, `neelStateOf`,
`neelStateOfS`, `heisenbergToyHamiltonianS`, `ladderIterateUp`,
`allAlignedStateS`, `totalSpinSOpPlus`/`totalSpinSOpMinus`,
`saturatedFerromagnetJointEigenspace`) is still a live declaration prefix with
surviving variants, and the `Theorem23*` module family is still 56 live modules
under `Quantum/SpinS/` (no declaration name carries that prefix).  Most of those
survivors keep their own rows in this index, but not all: of the 201 live
public declarations under the declaration stems just listed, 158 are named
verbatim in some row's first column, two only inside another row's prose, one
only inside the stem list just given, and 40 are named verbatim nowhere in this
file, though some of that last group are still named indirectly inside this
file's own abbreviated forms (brace families such as `_totalSpinSOp{1,2,3}` and
suffix elisions such as `/ _sq`).
For `ladderIterateUp_*` the survivors are even the
majority of the stem's variants: of the 17 declarations with that prefix that
the tree held before these deletions, 11 are still present.  Only the variants
enumerated above are gone.  Likewise,
deleted names of the form `tasaki_2_5_theorem_2_3_of_..._threaded_...` belonged
to the abandoned route and are not the live capstone `tasaki_2_5_theorem_2_3`.

<!-- legacy-source:end:72:109 -->
