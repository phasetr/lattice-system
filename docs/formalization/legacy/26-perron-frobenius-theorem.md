---
layout: page
title: "Legacy catalogue: Perron-Frobenius theorem (`Math/PerronFrobenius.lean`, `Math/PerronFrobeniusPrimitive.lean`, `Math/CollatzWielandt.lean`, `Math/PerronFrobeniusMain.lean`)"
permalink: /formalization/legacy/26-perron-frobenius-theorem/
---

# Legacy catalogue: Perron-Frobenius theorem (`Math/PerronFrobenius.lean`, `Math/PerronFrobeniusPrimitive.lean`, `Math/CollatzWielandt.lean`, `Math/PerronFrobeniusMain.lean`)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin models, Chapters 3–7, and spectral tools](/lattice-system/formalization/legacy/#group-spin-models)

<!-- legacy-source:start:1562:1587 -->
### Perron-Frobenius theorem (`Math/PerronFrobenius.lean`, `Math/PerronFrobeniusPrimitive.lean`, `Math/CollatzWielandt.lean`, `Math/PerronFrobeniusMain.lean`)

Perron-Frobenius theorem for nonneg irreducible/primitive matrices (Issue #405, closed).
The sorry in `exists_pos_eigenvec_max` is eliminated via the Collatz-Wielandt port (PRs A–C).

| Lean name | Statement | File |
|---|---|---|
| `Matrix.IsPrimitive.of_irreducible_pos_diagonal` | irreducible nonneg + positive diagonal → primitive (Seneta §1.1, Prop. 1.3, p. 17) | `Math/PerronFrobeniusPrimitive.lean` |
| `CollatzWielandt.collatzWielandtFn` | CW function `min_{i\|x_i>0} (Ax)_i/x_i` (Seneta §1.2, p. 27) | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.le_any_ratio` | `CW(x) ≤ (Ax)_i/x_i` for `x_i > 0` | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.le_mulVec` | fundamental inequality `CW(x)·x ≤ Ax` | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.smul_eq` | scale invariance `CW(cx) = CW(x)` for `c > 0` | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.upperSemicontinuousOn` | CW is upper-semicontinuous on stdSimplex | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.exists_maximizer` | CW attains its max on stdSimplex (EVT for USC, Seneta §1.2, p. 28) | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.eq_eigenvalue` | `CW(v) = r` when `Av = r·v`, `v > 0` | `Math/CollatzWielandt.lean` |
| `CollatzWielandt.lt_of_all_ratios_gt` | all ratios `> c` ⟹ `CW(x) > c` | `Math/CollatzWielandt.lean` |
| `PerronFrobeniusMain.pos_of_nonneg_eigenvec` | irreducible nonneg + `Av = μv`, `v ≥ 0`, `v ≠ 0` ⟹ `v > 0` (standard propagation argument) | `Math/PerronFrobeniusMain.lean` |
| `PerronFrobeniusMain.exists_positive_eigenvector_of_primitive` | primitive nonneg ⟹ ∃ `r > 0`, `v > 0` with `Av = rv` (Seneta §1.2, pp. 27–28) | `Math/PerronFrobeniusMain.lean` |
| `PerronFrobeniusMain.exists_positive_eigenvector_of_irreducible` | irreducible nonneg ⟹ ∃ `r > 0`, `v > 0` with `Av = rv` (Seneta §1.2, pp. 27–28) | `Math/PerronFrobeniusMain.lean` |
| `exists_pos_eigenvec_max` | (**sorry-free**) irreducible nonneg Hermitian ⟹ max eigenvalue has strictly positive eigenvector | `Math/PerronFrobenius.lean` |
| `pos_eigenvec_unique` | strictly positive eigenvector unique up to positive scalar | `Math/PerronFrobenius.lean` |
| `PerronFrobenius.eigenvec_proportional_of_pos_eigenvec` | **geometric simplicity of the Perron eigenvalue**: irreducible nonneg with a strictly positive eigenvector `v` at `μ` ⟹ every real eigenvector at `μ` is `s • v` for some scalar `s` (the `μ`-eigenspace is 1-dimensional). Perturbation trick: `v + t • u > 0` for small `t > 0` is an eigenvector at `μ`, hence `∝ v` by `pos_eigenvec_unique`, forcing `u ∝ v`. Used to show a Perron ground state is a joint eigenvector of any commuting operator (e.g. the total Casimir) | `Math/PerronFrobeniusSimple.lean` |

References: E. Seneta, *Non-negative Matrices and Markov Chains* (3rd ed.), Springer 2006, §1.2 (pp. 27–28);
or4nge19/MCMC: `MCMC/PF/LinearAlgebra/Matrix/PerronFrobenius/`.

<!-- legacy-source:end:1562:1587 -->

---

[← Heisenberg chain (Tasaki §3.5)](/lattice-system/formalization/legacy/25-heisenberg-chain-tasaki-3-5-part-02/) · [Catalogue](/lattice-system/formalization/legacy/) · [Spin-`S` Marshall–Lieb–Mattis on the magnetization sector (Tasaki §2.5 Theorem 2.2 generic S, sector form) →](/lattice-system/formalization/legacy/27-spin-marshall-lieb-mattis-on-the-magnetization-sector-tasa-part-01/)
