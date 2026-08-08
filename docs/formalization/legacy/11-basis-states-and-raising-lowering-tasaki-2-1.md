---
layout: page
title: "Legacy catalogue: Basis states and raising/lowering (Tasaki §2.1)"
permalink: /formalization/legacy/11-basis-states-and-raising-lowering-tasaki-2-1/
---

# Legacy catalogue: Basis states and raising/lowering (Tasaki §2.1)

> **Interim authority.** This lossless catalogue chunk remains authoritative for formalization status and capstone identification until Issue #5228. The version 1 JSON catalogue is still a non-authoritative prototype.

[Interim catalogue](/lattice-system/formalization/legacy/) › [Spin foundations and Tasaki Chapter 2](/lattice-system/formalization/legacy/#group-spin-foundations)

<!-- legacy-source:start:410:424 -->
### Basis states and raising/lowering (Tasaki §2.1)

Primary reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 eqs. (2.1.4), (2.1.5), (2.1.6), p. 14.

| Lean name | Statement | File |
|---|---|---|
| `spinHalfUp`, `spinHalfDown` | `\|ψ^↑⟩`, `\|ψ^↓⟩` as column vectors (Tasaki (2.1.6)) | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOp3_mulVec_spinHalfUp/Down` | `Ŝ^(3)` eigenvalue equations (Tasaki (2.1.4)) | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus`, `spinHalfOpMinus` | raising/lowering `Ŝ^±` | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus_eq_add`, `spinHalfOpMinus_eq_sub` | `Ŝ^± = Ŝ^(1) ± i · Ŝ^(2)` | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus/Minus_mulVec_spinHalfUp/Down` | raising/lowering actions (Tasaki (2.1.5)) | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus/Minus_conjTranspose` | `(Ŝ^±)† = Ŝ^∓` | `Quantum/SpinHalfBasis.lean` |
| `spinHalfOpPlus_commutator_spinHalfOpMinus` | `[Ŝ^+, Ŝ^-] = 2 · Ŝ^(3)` | `Quantum/SpinHalfBasis.lean` |

<!-- legacy-source:end:410:424 -->

---

[← Spin-`S` operators (general S ≥ 0, parameterised by `N = 2S : ℕ`)](/lattice-system/formalization/legacy/10-spin-operators-general-s-0-parameterised-by/) · [Catalogue](/lattice-system/formalization/legacy/) · [Basis states and raising/lowering for S = 1 (Tasaki §2.1) →](/lattice-system/formalization/legacy/12-basis-states-and-raising-lowering-for-s-1-tasaki-2-1/)
