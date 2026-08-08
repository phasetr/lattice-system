---
layout: page
title: "Legacy catalogue: Generic matrix-analysis helpers (`Math/MatrixAnalysis/`)"
permalink: /formalization/legacy/15-generic-matrix-analysis-helpers/
---

# Legacy catalogue: Generic matrix-analysis helpers (`Math/MatrixAnalysis/`)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:525:548 -->
### Generic matrix-analysis helpers (`Math/MatrixAnalysis/`)

Topic-organized generic linear-algebra facts extracted from the physics files where they had been
re-proved as private helpers (Issue [#4339](https://github.com/phasetr/lattice-system/issues/4339)).

| Lean name | Statement | File |
|---|---|---|
| `Matrix.isHermitian_sum` | a finite sum of Hermitian matrices is Hermitian | `Math/MatrixAnalysis/HermitianSum.lean` |
| `Matrix.IsHermitian.mul_of_commute` | the product of two commuting Hermitian matrices is Hermitian | `Math/MatrixAnalysis/HermitianSum.lean` |
| `Matrix.noncommProd_isHermitian` | a `Finset.noncommProd` of pairwise-commuting Hermitian matrices is Hermitian | `Math/MatrixAnalysis/NoncommProd.lean` |
| `Matrix.noncommProd_sq_of_sq_one` | a `Finset.noncommProd` of pairwise-commuting involutions is an involution | `Math/MatrixAnalysis/NoncommProd.lean` |
| `Matrix.noncommProd_mul_self_of_idempotent` | a `Finset.noncommProd` of pairwise-commuting idempotents is idempotent | `Math/MatrixAnalysis/NoncommProd.lean` |
| `Matrix.noncommProd_mulVec_eq_self` | a `Finset.noncommProd` of matrices each fixing `ψ` also fixes `ψ` | `Math/MatrixAnalysis/NoncommProd.lean` |
| `Matrix.IsHermitian.trace_im` | the trace of a Hermitian matrix is real | `Math/MatrixAnalysis/HermitianTrace.lean` |
| `Matrix.trace_mul_star_of_isHermitian` | `Tr(A·B)` of two Hermitian matrices is conjugation-invariant | `Math/MatrixAnalysis/HermitianTrace.lean` |
| `rayleighOnVec_mono` | Loewner monotonicity of the unnormalised energy quadratic form: `A ≤ B` implies `rayleighOnVec A v ≤ rayleighOnVec B v` for every `v` — the pointwise input to the eigenvalue comparison of **Tasaki Theorem A.7** (§A.2, p. 468) (PR #5149) | `Math/MatrixAnalysis/CourantFischer.lean` |

(The two trace helpers above are also listed in the Gibbs-state section where they are consumed; the
canonical definitions live in `Math/MatrixAnalysis/HermitianTrace.lean`.)

These are consumed by the Jordan–Wigner string / Hubbard hard-core projection layers (PR #4342),
replacing the per-file private copies in `Fermion/JWAbstract.lean`,
`Fermion/JordanWigner/Operators.lean`, and `Fermion/JordanWigner/Hubbard/HardcoreProjection.lean`.

<!-- legacy-source:end:525:548 -->

---

[← Multi-body operator space (abstract lattice)](/lattice-system/formalization/legacy/14-multi-body-operator-space-abstract-lattice/) · [Catalogue](/lattice-system/formalization/legacy/) · [Horsch–von der Linden low-lying states (Tasaki §3.4, Theorem 3.1) →](/lattice-system/formalization/legacy/16-horsch-von-der-linden-low-lying-states-tasaki-3-4-theorem--part-01/)
