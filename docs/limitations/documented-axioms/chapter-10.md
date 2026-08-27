---
layout: page
title: "Documented axioms: Tasaki Chapter 10"
permalink: /limitations/documented-axioms/chapter-10/
---

# Documented axioms: Tasaki Chapter 10

[Documented-axiom policy and entry index](/lattice-system/limitations/documented-axioms/)

<a id="entry-theorem-10-11"></a>

## Theorem 10.11 (Kubo–Kishi finite-temperature charge/pairing susceptibility bound)

**Tasaki §10.2.5, Theorem 10.11** (eqs. (10.2.52)-(10.2.56), pp. 368-369) is a
**documented axiom**, `theorem_10_11_kubo_kishi_susceptibility_bound`
(`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebKuboKishi.lean`, declaration
line 139).

- **Proved (axiom-free):** the surrounding finite-volume machinery — the
  Duhamel static susceptibility, the charge and pairing Fourier-mode
  observables (`chargeFourierMode`, `pairFieldFourierMode`), and the
  Theorem 10.4 hypotheses on the hopping matrix `T` (bipartite, real
  symmetric, connected) — are all real definitions, not axioms.
- **What the axiom statement literally asserts:** for the uniform repulsive
  Hubbard model (`U > 0`) on a bipartite, real-symmetric, connected hopping
  matrix `T` (Theorem 10.4's conditions except the electron-number one), at
  the half-filling chemical potential `μ = U/2`, for every `β > 0` and every
  wave number `k`, the charge susceptibility `χ^c_k(β, U/2) ≤ 1/U` and the
  on-site pairing susceptibility `χ^p_k(β, U/2) ≤ 2/U` (eq. (10.2.56)), both
  real-valued — ruling out charge-density-wave or superconducting long-range
  order at any finite temperature.
- **Axiom reason (documented):** Tasaki states this without proof, citing
  Kubo–Kishi, *Phys. Rev. B* **41**, 4866 (1990); this is the project's
  external-cite-only policy class (Tasaki records a result from the outside
  literature rather than proving it in the text), the same class as Theorem
  11.13 (Mielke).
- **Re-check condition:** would change only if a math-before-code
  transcription of the Kubo–Kishi Duhamel-susceptibility argument is
  completed in this repository.
- **Tracking:** master tracker #4718 (strict book-order axiom discharge). No
  dedicated discharge issue exists or is to be opened while Tasaki continues
  to state this without proof.
