---
layout: page
title: "Legacy long-form records: Fermions and Hubbard models, part 1"
permalink: /formalization/legacy/details/group-fermions-hubbard-part-01/
---

# Legacy long-form records: Fermions and Hubbard models, part 1

> **Interim authority.** These records contain long statement and implementation-history cells moved from the legacy catalogue tables for readability. Each record is linked exactly once from its original table position.

[Interim catalogue](/lattice-system/formalization/legacy/)

<a id="record-2596"></a>
## Record from former line 2596

**Lean name:** <!-- legacy-detail-lean:start:2596 -->`fermionTotalSpinSquared_eq_cartesianSqSum` / `attractiveHubbardFullSectorGround` / `attractiveHubbardFullSectorGround_le_balanced` / `attractiveHubbardFullSectorGround_unique_singlet`<!-- legacy-detail-lean:end:2596 -->

**File:** <!-- legacy-detail-file:start:2596 -->`Fermion/JordanWigner/Hubbard/LiebAttractiveFullSectorUnique.lean`, `Math/AngularMomentum/Multiplet.lean`, `Math/CommutingHermitianEigenvector.lean` (PR #4946)<!-- legacy-detail-file:end:2596 -->

**Statement and implementation chronicle:**

<!-- legacy-detail:start:2596 -->
**The full `Ne`-sector ground eigenspace is the balanced singlet** (Tasaki §10.2.1 Theorem 10.2,
full-sector lift, PR-D' #4852): with `E_bal = E_full` in hand, the whole-sector ground eigenspace
`G_full := (Ĥ = E_full) ⊓ (N̂ = Ne)` is shown to be `≤ 1`-dimensional and a spin singlet. `Ŝ³`
(`fermionTotalSpinZ`) commutes with `Ĥ` and `N̂`, so it preserves `G_full`, and (being diagonal on
the computational basis) its eigenspaces span `⊤`;

hence `Submodule.eq_iSup_inf_genEigenspace` gives the weight decomposition `G_full = ⨆ μ, G_full ⊓
eigenspace(Ŝ³, μ)` (mirror of the t-J `tJ_groundSubmodule_eq_iSup_inf_eigenspace`). Each
nonzero-weight block is `⊥`: diagonalising the Casimir `Ŝ²` inside a weight-`μ` block
(`exists_eigenvector_in_invariant_submodule`) yields a joint `(Ĥ, N̂, Ŝ³ = m, Ŝ² = Jr(Jr+1))`
eigenstate `χ ≠ 0` with `m ≠ 0`, so `Jr ≥ |m| > 0`;

for even `Ne` the weight `m` is an integer (`N̂_↑ = Ne/2 + m ∈ ℕ`), so the SU(2) multiplet of `χ`
(`ham_su2_multiplet_companion`, Theorem A.16, whose commuting-operator tracker propagates both `Ĥ`
and `N̂` through the ladder) contains a nonzero **weight-0** companion `Ψ` at `E_full` and number
`Ne` — a balanced state at `E_bal = E_full`, hence a singlet `Ŝ²Ψ = 0`
(`balancedGround_totalSpinSquared_eigenvalue_zero`), contradicting `Ŝ²Ψ = Jr(Jr+1)Ψ ≠ 0`. Thus
`G_full ⊆ (Ŝ³ = 0)`, i.e. `G_full ≤ balancedGroundEigenspace`, giving `finrank ℂ G_full ≤ 1`
(`balanced_ground_eigenspace_finrank_le_one`) and the singlet property. The Casimir identity
`(Ŝ_tot)² = (Ŝ⁽¹⁾)² + (Ŝ⁽²⁾)² + (Ŝ³)²` (`fermionTotalSpinSquared_eq_cartesianSqSum`, via the ladder
commutator `Ŝ⁺Ŝ⁻ − Ŝ⁻Ŝ⁺ = 2Ŝ³`) bridges the engine's Casimir and `fermionTotalSpinSquared`.
Axiom-free. Plain-space uniqueness+singlet milestone feeding the eventual Euclidean
`IsUniqueGroundStateOn` discharge (PR-E).
<!-- legacy-detail:end:2596 -->
