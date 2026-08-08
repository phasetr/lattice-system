---
layout: page
title: "Legacy catalogue: Single-site Pauli operators"
permalink: /formalization/legacy/01-single-site-pauli-operators/
---

# Legacy catalogue: Single-site Pauli operators

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:229:243 -->
### Single-site Pauli operators

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eq. (2.1.8), p. 15. Cross-checked with Nielsen-Chuang
§2.1.3 Figure 2.2 (pp. 65-66, definitions), Ex. 2.19 (p. 70,
Hermiticity), Ex. 2.41 (p. 78, `(σ^α)² = I` and anticommutation),
Ex. 2.40 (p. 77, commutator, whence the cyclic products).

| Lean name | Statement | File |
|---|---|---|
| `pauliX/Y/Z_isHermitian` | `(σ^α)† = σ^α` | `Quantum/Pauli.lean` |
| `pauliX/Y/Z_mul_self` | `(σ^α)² = I` | `Quantum/Pauli.lean` |
| `pauliX_mul_pauliY` etc. | `σ^x σ^y = i·σ^z` (cyclic) | `Quantum/Pauli.lean` |
| `pauliX_anticomm_pauliY` etc. | `σ^α σ^β + σ^β σ^α = 0` (α ≠ β) | `Quantum/Pauli.lean` |

<!-- legacy-source:end:229:243 -->

---

← Start · [Catalogue](/lattice-system/formalization/legacy/) · [Spin-1/2 operators (Tasaki §2.1) →](/lattice-system/formalization/legacy/02-spin-1-2-operators-tasaki-2-1/)
