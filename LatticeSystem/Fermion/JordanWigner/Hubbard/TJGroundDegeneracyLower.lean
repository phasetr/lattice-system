import LatticeSystem.Fermion.JordanWigner.Hubbard.TJMaximalSpinGroundState
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaConnectivity

/-!
# Tasaki 11.5: ground degeneracy lower bound (Prop 11.24 E4)

The maximal-spin highest-weight ground state `Ω` (from
`tJ_exists_maximalSpin_highestWeight_groundState`) generates, via the SU(2) lowering tower
`highestWeight_spinMultiplet_general`, `Ne+1` linearly independent states `(Ŝ⁻)^k Ω`.  Since `Ŝ⁻`
commutes with `Ĥ_tJ` and `N̂` and preserves the hard-core subspace, every tower member is again a
ground state in `groundSubmoduleAtFilling`.  Hence `Ne + 1 ≤ finrank` of the ground subspace — the
degeneracy lower bound.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- **Ground degeneracy lower bound.**  The d=1 ferromagnetic t-J ground subspace at odd filling
`Ne < N+1` has dimension at least `Ne + 1` (the maximal-spin multiplet). -/
theorem tJ_groundSubmodule_finrank_ge (hpos : 0 < N) (Ne : ℕ) (hNeLt : Ne < N + 1) (hodd : Odd Ne)
    (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) :
    Ne + 1 ≤ finrank ℂ
      ↥(groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne) := by
  classical
  obtain ⟨Ω, hΩne, hΩtop, hΩsz, hΩH, hΩhc, hΩN⟩ :=
    tJ_exists_maximalSpin_highestWeight_groundState hpos Ne hNeLt hodd τ J hτ hJ
  obtain ⟨hLI, _⟩ := highestWeight_spinMultiplet_general N Ne Ω hΩne hΩtop hΩsz
  set G := groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne with hG
  set ge : ℝ := groundEnergyAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne with hge
  -- each tower member is a ground state
  have hmem : ∀ k : Fin (Ne + 1),
      ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω ∈ G := by
    intro k
    have hHk : (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec
        (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω) =
        ((ge : ℂ)) • (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω) := by
      have hcomm : Commute (tJHamiltonian N (cycleGraph (N + 1)) τ J)
          ((fermionTotalSpinMinus N) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_tJHamiltonian N (cycleGraph (N + 1)) τ J).symm).pow_right _
      rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hΩH, Matrix.mulVec_smul]
    have hNk : (fermionTotalNumber (2 * N + 1)).mulVec
        (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω) =
        (Ne : ℂ) • (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω) := by
      have hcomm : Commute (fermionTotalNumber (2 * N + 1))
          ((fermionTotalSpinMinus N) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_fermionTotalNumber N).symm).pow_right _
      rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hΩN, Matrix.mulVec_smul]
    rw [hG, groundSubmoduleAtFilling, Submodule.mem_inf, Submodule.mem_inf,
      Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply]
    exact ⟨⟨hHk, hNk⟩, fermionTotalSpinMinus_pow_mulVec_mem_hardcore N (k : ℕ) hΩhc⟩
  -- the tower is linearly independent inside G, so finrank ≥ Ne + 1
  have hGLI : LinearIndependent ℂ (fun k : Fin (Ne + 1) =>
      (⟨((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω, hmem k⟩ : G)) :=
    LinearIndependent.of_comp G.subtype hLI
  have := hGLI.fintype_card_le_finrank
  simpa using this

end LatticeSystem.Fermion
