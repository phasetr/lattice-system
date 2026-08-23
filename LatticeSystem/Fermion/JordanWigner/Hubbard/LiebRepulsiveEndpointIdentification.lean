import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSymmetricHomotopy
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSuperexchangeReducedInverse

/-!
# Symmetric endpoint identification (Tasaki §10.2.2, PR-13a scaffolding)

Seventeenth installment of the Theorem 10.4 discharge arc (issue #5320). **Red scaffold only**:
every statement below is asserted with `sorry`; the type signatures are the deliverable of this
commit, proofs are dev-implement's task. Scope per the "PR-13 design round"/"メイン判断"
(2026-08-23) sections of `.self-local/active/issue-5320.md`.

## Main results (all `sorry`)

* `symmetricHomotopyHamiltonian_one_eq_uniform` — the `s = 1` endpoint of PR-12b's symmetric-form
  homotopy is exactly the uniform-`U = 1` symmetric repulsive Hubbard Hamiltonian on the endpoint
  hopping matrix `liebEndpointHopping A T lam`, since `homotopyHopping … 1 = liebEndpointHopping A T
  lam` and `homotopyOnSiteFn U 1 ≡ 1`.
* `configSectorCompress_symmetricHomotopyHamiltonian_one_eq_perturbedHamiltonian_sub_smul` — the
  compressed form of that endpoint on the half-filled fixed-`Ŝ³` sector: combining the endpoint
  identity above with PR-12a's `symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber`
  (at `U ≡ 1`) and PR-6's `homotopyHamiltonian_one_compressed_eq_perturbedHamiltonian`, the
  compressed number operator `Σ_x n̂_x` collapses to `(N+1) • 1` on the sector, so the whole shift
  is a genuine scalar multiple of `1` — the shape PR-11a's
  `isUniqueGroundStateOn_sub_smul_one_iff` (`Math/MatrixAnalysis/SubmatrixGroundState.lean`) needs,
  with no sector-restricted shift lemma required (superseding the earlier PR-12 design note).

The generic block-transport lemma
`isUniqueGroundStateOn_coordinateSpan_iff_submatrix`
(`Math/MatrixAnalysis/BlockTransport.lean`) has been generalized in place from the block-diagonal
hypothesis `hblock : H = P̂ · H · P̂` to the weaker invariance hypothesis
`hInv : ∀ i j, P j → ¬ P i → H i j = 0` in the same commit (its sole call site,
`LiebRepulsiveSectorAssembly.lean:154`, is updated accordingly); no new file is needed for that
generalization. `Math/MatrixAnalysis/MinEnergyOnSubspace.lean`'s `minEnergyOn_add_const_smul_one`
(reference-0 since PR-5) is deleted in the same commit, per its own doc comment's stipulation.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2, p. 353.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators

variable {N : ℕ}

/-! ## The `s = 1` endpoint of the symmetric-form homotopy -/

/-- **The symmetric-form homotopy's `s = 1` endpoint is the uniform-`U = 1` symmetric repulsive
Hubbard Hamiltonian on the endpoint hopping matrix.** `homotopyHopping T (liebEndpointHopping A T
lam) 1 = liebEndpointHopping A T lam` and `homotopyOnSiteFn U 1 ≡ 1` (`homotopyOnSite _ 1 = 1`),
so `symmetricHomotopyHamiltonian N A T U lam 1` reduces to `symmetricRepulsiveHubbardHamiltonian N
(liebEndpointHopping A T lam) (fun _ => 1)`. -/
theorem symmetricHomotopyHamiltonian_one_eq_uniform (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (lam : ℝ) :
    symmetricHomotopyHamiltonian N A T U lam 1
      = symmetricRepulsiveHubbardHamiltonian N (liebEndpointHopping A T lam) (fun _ => 1) := by
  sorry

/-! ## Compression to the half-filled fixed-`Ŝ³` sector -/

/-- **The compressed `s = 1` endpoint is the compressed perturbed Hamiltonian up to a genuine
scalar shift.** On `configSector N (liebHalfFillingPred N nUp)`, PR-12a's
`symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber` (at `U ≡ 1`) expands the endpoint
interaction as `liebPerturbationH0 N − (1/2) • N̂ + ((N+1)/4) • 1`; since `N̂` compresses to
`(N+1) • 1` on this sector, the whole offset from `perturbedHamiltonian (liebPerturbationH0
Compressed N nUp) (liebPerturbationVCompressed N nUp A T) lam` collapses to the explicit scalar
`((N+1)/4 : ℝ) • 1`. This is the shape PR-11a's `isUniqueGroundStateOn_sub_smul_one_iff` consumes
directly; no sector-restricted shift lemma is needed. -/
theorem configSectorCompress_symmetricHomotopyHamiltonian_one_eq_perturbedHamiltonian_sub_smul
    (N nUp : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (lam : ℝ) :
    configSectorCompress N (liebHalfFillingPred N nUp)
        (symmetricHomotopyHamiltonian N A T U lam 1)
      = LatticeSystem.Math.perturbedHamiltonian (liebPerturbationH0Compressed N nUp)
          (liebPerturbationVCompressed N nUp A T) lam
        - (((N : ℝ) + 1) / 4 : ℝ) • (1 : Matrix _ _ ℂ) := by
  sorry

end LatticeSystem.Fermion
