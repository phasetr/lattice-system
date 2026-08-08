---
layout: page
title: "Legacy catalogue: Polynomial-basis decomposition for S = 1 (Tasaki §2.1 Problem 2.1.a, S = 1)"
permalink: /formalization/legacy/08-polynomial-basis-decomposition-for-s-1-tasaki-2-1-problem-/
---

# Legacy catalogue: Polynomial-basis decomposition for S = 1 (Tasaki §2.1 Problem 2.1.a, S = 1)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:337:352 -->
### Polynomial-basis decomposition for S = 1 (Tasaki §2.1 Problem 2.1.a, S = 1)

Primary reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, §2.1 Problem 2.1.a, p. 15 + solution S.1, p. 493.

| Lean name | Statement | File |
|---|---|---|
| `spinOneProj{Plus,Zero,Minus}` | the three diagonal projectors `\|ψ^σ⟩⟨ψ^σ\|` (σ ∈ {+1, 0, -1}) | `Quantum/SpinOneDecomp.lean` |
| `spinOneProj{Plus,Zero,Minus}_eq_polynomial` | each diagonal projector equals a polynomial in `Ŝ^(3)` (Lagrange interpolation) | `Quantum/SpinOneDecomp.lean` |
| `spinOneUnit{01,02,10,12,20,21}` | the six off-diagonal matrix units `\|ψ^τ⟩⟨ψ^σ\|` (τ ≠ σ) | `Quantum/SpinOneDecomp.lean` |
| `spinOneUnit{01,12}_eq_polynomial` | `(1/√2) Ŝ^- · P_σ` for the two single-step lowering units | `Quantum/SpinOneDecomp.lean` |
| `spinOneUnit{10,21}_eq_polynomial` | `(1/√2) Ŝ^+ · P_σ` for the two single-step raising units | `Quantum/SpinOneDecomp.lean` |
| `spinOneUnit02_eq_polynomial` | `(1/2) (Ŝ^-)² · P_+` for the double-step lowering unit | `Quantum/SpinOneDecomp.lean` |
| `spinOneUnit20_eq_polynomial` | `(1/2) (Ŝ^+)² · P_-` for the double-step raising unit | `Quantum/SpinOneDecomp.lean` |
| `spinOne_decomposition` | every 3×3 complex matrix is a linear combination of the 9 matrix units (entry-wise); combined with the polynomial expressions above this gives Tasaki Problem 2.1.a for `S = 1` | `Quantum/SpinOneDecomp.lean` |

<!-- legacy-source:end:337:352 -->

---

[← Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2)](/lattice-system/formalization/legacy/07-pauli-basis-decomposition-tasaki-2-1-problem-2-1-a-s-1-2/) · [Catalogue](/lattice-system/formalization/legacy/) · [S = 1 matrix representations (Tasaki §2.1 eq. (2.1.9)) →](/lattice-system/formalization/legacy/09-s-1-matrix-representations-tasaki-2-1-eq-2-1-9/)
