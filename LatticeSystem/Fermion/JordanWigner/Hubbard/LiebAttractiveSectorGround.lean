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
(`configSectorCompress`, `configSectorExpansion`, the eigenvector lift
`configSectorExpansion_of_compress_eigen`) is generic over any number-conserving operator.
This module supplies the missing charge-conservation input for the attractive Hamiltonian and
instantiates the lift.

## Main results

* `hubbardOnSiteInteractionSite_commute_fermionTotalNumber` — the site interaction conserves `N̂`.
* `attractiveHubbardHamiltonian_commute_fermionTotalNumber` — the attractive `Ĥ` conserves `N̂`.
* `fermionTotal{Up,Down}Number_commute_hubbardOnSiteInteractionSite` — the site interaction
  conserves each spin number `N̂_↑`, `N̂_↓`.
* `attractiveHubbardHamiltonian_commute_fermionTotal{Up,Down}Number` — the attractive `Ĥ`
  conserves each spin number: `[Ĥ, N̂_↑] = [Ĥ, N̂_↓] = 0`.
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

/-- `N_↑` commutes with the site-dependent on-site interaction `Σ_x V_x n̂_{x,↑} n̂_{x,↓}`: every
summand is a product of pairwise-commuting number operators (mirror of the uniform-coupling
`fermionTotalUpNumber_commute_hubbardOnSiteInteraction`). -/
theorem fermionTotalUpNumber_commute_hubbardOnSiteInteractionSite (V : Fin (N + 1) → ℂ) :
    Commute (fermionTotalUpNumber N) (hubbardOnSiteInteractionSite N V) := by
  unfold fermionTotalUpNumber hubbardOnSiteInteractionSite
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.smul_right ?_ (V i)
  unfold fermionUpNumber fermionDownNumber
  refine Commute.mul_right ?_ ?_
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 0) (spinfulIndex N i 0)
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 0) (spinfulIndex N i 1)

/-- `N_↓` commutes with the site-dependent on-site interaction `Σ_x V_x n̂_{x,↑} n̂_{x,↓}` (mirror
of the uniform-coupling `fermionTotalDownNumber_commute_hubbardOnSiteInteraction`). -/
theorem fermionTotalDownNumber_commute_hubbardOnSiteInteractionSite (V : Fin (N + 1) → ℂ) :
    Commute (fermionTotalDownNumber N) (hubbardOnSiteInteractionSite N V) := by
  unfold fermionTotalDownNumber hubbardOnSiteInteractionSite
  refine Commute.sum_left _ _ _ (fun k _ => ?_)
  refine Commute.sum_right _ _ _ (fun i _ => ?_)
  refine Commute.smul_right ?_ (V i)
  unfold fermionUpNumber fermionDownNumber
  refine Commute.mul_right ?_ ?_
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 1) (spinfulIndex N i 0)
  · exact fermionMultiNumber_commute (2 * N + 1)
      (spinfulIndex N k 1) (spinfulIndex N i 1)

/-- The **attractive Hubbard Hamiltonian conserves the spin-up number**: `[Ĥ, N̂_↑] = 0`. Both the
kinetic term and the site attraction commute with `N̂_↑` (mirror of
`attractiveHubbardHamiltonian_commute_fermionTotalNumber`). -/
theorem attractiveHubbardHamiltonian_commute_fermionTotalUpNumber
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    Commute (attractiveHubbardHamiltonian N T U) (fermionTotalUpNumber N) := by
  unfold attractiveHubbardHamiltonian attractiveHubbardInteraction
  exact (fermionTotalUpNumber_commute_hubbardKinetic N _).symm.add_left
    (fermionTotalUpNumber_commute_hubbardOnSiteInteractionSite _).symm

/-- The **attractive Hubbard Hamiltonian conserves the spin-down number**: `[Ĥ, N̂_↓] = 0` (mirror
of `attractiveHubbardHamiltonian_commute_fermionTotalNumber`). -/
theorem attractiveHubbardHamiltonian_commute_fermionTotalDownNumber
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    Commute (attractiveHubbardHamiltonian N T U) (fermionTotalDownNumber N) := by
  unfold attractiveHubbardHamiltonian attractiveHubbardInteraction
  exact (fermionTotalDownNumber_commute_hubbardKinetic N _).symm.add_left
    (fermionTotalDownNumber_commute_hubbardOnSiteInteractionSite _).symm

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
          = ((hermitianMinEigenvalue (configSectorCompress_isHermitian
              (hubbardNumberSectorPred N Ne)
              (attractiveHubbardHamiltonian_isHermitian T U hT)) : ℝ) : ℂ) • φ := by
  classical
  set hHW := configSectorCompress_isHermitian (hubbardNumberSectorPred N Ne)
    (attractiveHubbardHamiltonian_isHermitian T U hT) with hHWd
  obtain ⟨c, hc0, hceig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hHW
  set Φ := configSectorExpansion N (hubbardNumberSectorPred N Ne) c with hΦ
  have hΦW : Φ ∈ hubbardSectorWSubmodule N Ne := hubbardSectorExpansion_mem Ne c
  refine ⟨Φ, configSectorExpansion_ne_zero (hubbardNumberSectorPred N Ne) hc0, ?_, ?_⟩
  · rw [← mem_hubbardSectorWSubmodule_iff]; exact hΦW
  · have hApres := hubbardNumberSector_supported_of_mem Ne
      (preservesHubbardSectorW_attractive Ne T U Φ hΦW)
    exact configSectorExpansion_of_compress_eigen (hubbardNumberSectorPred N Ne) hApres hceig

end LatticeSystem.Fermion
