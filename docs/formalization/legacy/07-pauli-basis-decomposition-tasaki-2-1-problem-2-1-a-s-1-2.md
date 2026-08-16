---
layout: page
title: "Legacy catalogue: Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2)"
permalink: /formalization/legacy/07-pauli-basis-decomposition-tasaki-2-1-problem-2-1-a-s-1-2/
---

# Legacy catalogue: Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:325:336 -->
### Pauli-basis decomposition (Tasaki §2.1 Problem 2.1.a, S = 1/2)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a, p. 15.

| Lean name | Statement | File |
|---|---|---|
| `pauliCoeff{0,1,2,3}` | explicit coefficient functions | `Quantum/SpinHalfDecomp.lean` |
| `pauli_decomposition` | `A = Σᵢ cᵢ · σ^(i)` | `Quantum/SpinHalfDecomp.lean` |
| `spinHalf_decomposition` | same via `Ŝ^(α) = σ^(α) / 2` | `Quantum/SpinHalfDecomp.lean` |
| `pauli_linearIndep` | `{1, σ^x, σ^y, σ^z}` is linearly independent | `Quantum/SpinHalfDecomp.lean` |

<!-- legacy-source:end:325:336 -->

## Authoritative supplemental implementation record (spin-1/2 Pauli-basis decomposition module)

This section is maintained by hand, lies outside the migrated catalogue block above, and records
the current state of every row of that block. The migrated catalogue block is a frozen historical
record — it is pinned byte-for-byte by `scripts/check_docs_hierarchy.py` and is never edited for
later relocations or deletions — so its rows describe the library as it stood at migration time.

The module `Quantum/SpinHalfDecomp.lean` has been removed in full, and with it all four rows of the
block above: `pauliCoeff{0,1,2,3}`, `pauli_decomposition`, `spinHalf_decomposition` and
`pauli_linearIndep`. No row of the block has a member left in the library.

Tasaki §2.1 Problem 2.1.a itself is unaffected. It is formalized for every spin in
`spinS_adjoin_eq_top (N : ℕ)` (`Quantum/SpinS/SpanningTheorem.lean`), the 🎯 capstone catalogued on
the [spin-`S` operators page](/lattice-system/formalization/legacy/10-spin-operators-general-s-0-parameterised-by/),
which states `Algebra.adjoin ℂ {Ŝ^(1)_N, Ŝ^(2)_N, Ŝ^(3)_N} = ⊤`. Instantiating it at `N := 1` gives
the `S = 1/2` claim, and the three bridges `spinSOp{1,2,3}_one_eq_spinHalfOp{1,2,3}`
(`Quantum/SpinS/SpinHalfSpecialization.lean`) rewrite that instance into the concrete `spinHalfOp`
vocabulary in one line, so the retired module's book content is recoverable without new API. The
residual content that the general theorem does not carry — the explicit coefficient formulas
`pauliCoeff0..3` and the linear independence of `{1, σ^x, σ^y, σ^z}` — is not part of Problem 2.1.a,
which asks only that every operator be a polynomial in the spin operators.

Retained, and deliberately so: `pauliX_eq_two_smul_spinHalfOp1`, `pauliY_eq_two_smul_spinHalfOp2`
and `pauliZ_eq_two_smul_spinHalfOp3` (`Quantum/SpinHalf.lean`), whose only consumer was the retired
module. They are the library's only rendering of Tasaki eq. (2.1.8) `σ^(α) = 2 Ŝ^(α)`, catalogued on
the [spin-1/2 operators page](/lattice-system/formalization/legacy/02-spin-1-2-operators-tasaki-2-1/),
and no public generic states them: the spin-`S` bridges run the other way
(`spinSOp1 1 = spinHalfOp1`) and `pauliX` is a spin-1/2-only object. They keep their statements as
book-equation coverage, with no test reference manufactured for them.

---

[← 3D rotation matrices `R^(α)_π` (Tasaki §2.1 eq. (2.1.28))](/lattice-system/formalization/legacy/06-3d-rotation-matrices-tasaki-2-1-eq-2-1-28/) · [Catalogue](/lattice-system/formalization/legacy/) · [Polynomial-basis decomposition for S = 1 (Tasaki §2.1 Problem 2.1.a, S = 1) →](/lattice-system/formalization/legacy/08-polynomial-basis-decomposition-for-s-1-tasaki-2-1-problem-/)
