import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingGroundEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral
import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism
import LatticeSystem.Fermion.JordanWigner.Hubbard.NagaokaConnectivity

/-!
# Tasaki 11.5.3: half-filling ground degeneracy lower bound (Theorem 11.26 PR3h)

At half filling `Ne = N + 1` the maximal-spin reference is the all-up state `|↑…↑⟩`, a
highest-weight state for the total spin (`Ŝ⁺_tot |↑…↑⟩ = 0`, `Ŝ³_tot |↑…↑⟩ = ((N+1)/2) |↑…↑⟩`).
It is a ground
state (`Ĥ_tJ |↑…↑⟩ = 0 = groundEnergy · |↑…↑⟩`, `N̂ = N+1`, hard-core), so the SU(2) lowering tower
`highestWeight_spinMultiplet_general` produces `N + 2` linearly independent ground states
`(Ŝ⁻_tot)^k |↑…↑⟩`.  Hence:

* `tJ_halfFilling_groundSubmodule_finrank_ge` — `N + 2 ≤ finrank` of the half-filling ground
  subspace (the maximal-spin `(N+2)`-fold multiplet).

This is the lower half of the half-filling case of Theorem 11.26 (the ferromagnetic-Heisenberg
boundary `Ne = N+1`); the matching upper bound `finrank ≤ N + 2` follows in a later PR.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- **Half-filling ground degeneracy lower bound.**  The d=1 ferromagnetic t-J ground subspace at
half filling `Ne = N+1` has dimension at least `N + 2` (the maximal-spin `(N+2)`-fold multiplet
generated from the all-up state by the SU(2) lowering tower). -/
theorem tJ_halfFilling_groundSubmodule_finrank_ge (τ J : ℝ) (hJ : 0 < J) :
    N + 2 ≤ finrank ℂ
      ↥(groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1)) := by
  classical
  set Ω : (Fin (2 * N + 2) → Fin 2) → ℂ := hubbardAllUpState N with hΩ
  have hΩne : Ω ≠ 0 := hubbardAllUpState_ne_zero N
  have hΩtop : (fermionTotalSpinPlus N).mulVec Ω = 0 := fermionTotalSpinPlus_mulVec_allUpState N
  have hΩsz : (fermionTotalSpinZ N).mulVec Ω = (((N + 1 : ℕ) : ℂ) / 2) • Ω :=
    fermionTotalSpinZ_mulVec_allUpState N
  obtain ⟨hLI, _⟩ := highestWeight_spinMultiplet_general N (N + 1) Ω hΩne hΩtop hΩsz
  set G := groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1) with hG
  -- each tower member is a ground state (energy `0`, `N+1` electrons, hard-core)
  have hmem : ∀ k : Fin (N + 1 + 1),
      ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω ∈ G := by
    intro k
    have hHk : (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec
        (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω) = 0 := by
      have hcomm : Commute (tJHamiltonian N (cycleGraph (N + 1)) τ J)
          ((fermionTotalSpinMinus N) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_tJHamiltonian N (cycleGraph (N + 1)) τ J).symm).pow_right _
      rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hΩ,
        tJHamiltonian_mulVec_allUpState_eq_zero, Matrix.mulVec_zero]
    have hNk : (fermionTotalNumber (2 * N + 1)).mulVec
        (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω) =
        (((N + 1 : ℕ) : ℂ)) • (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω) := by
      have hcomm : Commute (fermionTotalNumber (2 * N + 1))
          ((fermionTotalSpinMinus N) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_fermionTotalNumber N).symm).pow_right _
      rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hΩ,
        fermionTotalNumber_mulVec_allUpState, Matrix.mulVec_smul]
    rw [hG, groundSubmoduleAtFilling, Submodule.mem_inf, Submodule.mem_inf,
      Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply]
    refine ⟨⟨?_, hNk⟩, fermionTotalSpinMinus_pow_mulVec_mem_hardcore N (k : ℕ)
      (hΩ ▸ hubbardAllUpState_mem_hardcore N)⟩
    rw [tJ_groundEnergyAtFilling_eq_zero τ J hJ, Complex.ofReal_zero, zero_smul]
    exact hHk
  -- the tower is linearly independent inside `G`, so `finrank ≥ N + 2`
  have hGLI : LinearIndependent ℂ (fun k : Fin (N + 1 + 1) =>
      (⟨((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω, hmem k⟩ : G)) :=
    LinearIndependent.of_comp G.subtype hLI
  have := hGLI.fintype_card_le_finrank
  simpa using this

end LatticeSystem.Fermion
