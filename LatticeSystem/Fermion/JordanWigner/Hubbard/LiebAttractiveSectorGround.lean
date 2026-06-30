import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHamiltonianHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUVariationalCore

/-!
# An `Ne`-electron sector ground vector for the attractive Hubbard model (Tasaki §10.2.4)

Layer PR40e-pre1 toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The Lieb
spin-reflection-positivity argument lives on the fixed electron-number sector, so it needs a
ground vector of the **site-dependent attractive** Hamiltonian
`attractiveHubbardHamiltonian N T U` that genuinely sits in the `Ne`-electron sector
(`N̂ φ = Ne·φ`), with energy the minimum eigenvalue of the *sector compression* (not the full
Hamiltonian).

The existing fixed-sector machinery in `HubbardImpossibilityLowUVariationalCore.lean`
(`hubbardSectorCompress`, `hubbardSectorExpansion`, the eigenvector lift
`mulVec_hubbardSectorExpansion_of_compress_eigen`) is generic over any number-conserving operator.
This module supplies the missing charge-conservation input for the attractive Hamiltonian and
instantiates the lift.

## Main results

* `hubbardOnSiteInteractionSite_commute_fermionTotalNumber` — the site interaction conserves `N̂`.
* `attractiveHubbardHamiltonian_commute_fermionTotalNumber` — the attractive `Ĥ` conserves `N̂`.
* `preservesHubbardSectorW_attractive` — `Ĥ` preserves the `Ne`-sector `W`-submodule.
* `exists_attractive_sector_ground` — a nonzero `Ne`-sector eigenvector at the sector-compression
  minimum eigenvalue.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.10), pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The site-dependent on-site interaction `Σ_x V_x n̂_{x,↑} n̂_{x,↓}` commutes with the total
number operator `N̂`: each density–density term does. -/
theorem hubbardOnSiteInteractionSite_commute_fermionTotalNumber (V : Fin (N + 1) → ℂ) :
    Commute (hubbardOnSiteInteractionSite N V) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardOnSiteInteractionSite
  refine Commute.sum_left _ _ _ (fun i _ => ?_)
  exact (fermionDensityDensity_commute_fermionTotalNumber (2 * N + 1)
    (spinfulIndex N i 0) (spinfulIndex N i 1)).smul_left (V i)

/-- The **attractive Hubbard Hamiltonian conserves charge**: `Commute Ĥ N̂` (kinetic and site
interaction each commute with `N̂`). -/
theorem attractiveHubbardHamiltonian_commute_fermionTotalNumber
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    Commute (attractiveHubbardHamiltonian N T U) (fermionTotalNumber (2 * N + 1)) := by
  unfold attractiveHubbardHamiltonian attractiveHubbardInteraction
  exact (hubbardKinetic_commute_fermionTotalNumber N _).add_left
    (hubbardOnSiteInteractionSite_commute_fermionTotalNumber _)

/-- The attractive Hamiltonian **preserves the `Ne`-sector `W`-submodule** — the reusable
hypothesis of the eigenvector lift. -/
theorem preservesHubbardSectorW_attractive (Ne : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    PreservesHubbardSectorW N Ne (attractiveHubbardHamiltonian N T U) := by
  intro v hv
  rw [mem_hubbardSectorWSubmodule_iff] at hv ⊢
  rw [Matrix.mulVec_mulVec,
    ← (attractiveHubbardHamiltonian_commute_fermionTotalNumber T U).eq,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- **An `Ne`-electron sector ground vector.** For symmetric real hopping `T` and any site
attraction `U`, there is a nonzero vector `φ` in the `Ne`-electron sector (`N̂ φ = Ne·φ`) that is an
eigenvector of the attractive Hamiltonian at the *sector compression's* minimum eigenvalue. -/
theorem exists_attractive_sector_ground (Ne : ℕ) [Nonempty (hubbardSectorConfig N Ne)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT : ∀ i j, T i j = T j i) :
    ∃ φ : (Fin (2 * N + 2) → Fin 2) → ℂ, φ ≠ 0
      ∧ (fermionTotalNumber (2 * N + 1)).mulVec φ = (Ne : ℂ) • φ
      ∧ (attractiveHubbardHamiltonian N T U).mulVec φ
          = ((hermitianMinEigenvalue (hubbardSectorCompress_isHermitian Ne
              (attractiveHubbardHamiltonian_isHermitian T U hT)) : ℝ) : ℂ) • φ := by
  classical
  set hHW := hubbardSectorCompress_isHermitian Ne (attractiveHubbardHamiltonian_isHermitian T U hT)
    with hHWd
  obtain ⟨c, hc0, hceig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hHW
  refine ⟨hubbardSectorExpansion N Ne c, hubbardSectorExpansion_ne_zero Ne hc0, ?_, ?_⟩
  · have hmem := hubbardSectorExpansion_mem Ne c
    rwa [mem_hubbardSectorWSubmodule_iff] at hmem
  · exact mulVec_hubbardSectorExpansion_of_compress_eigen Ne
      (preservesHubbardSectorW_attractive Ne T U) hceig

end LatticeSystem.Fermion
