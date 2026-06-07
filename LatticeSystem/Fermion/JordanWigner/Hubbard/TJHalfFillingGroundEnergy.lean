import LatticeSystem.Fermion.JordanWigner.Hubbard.TJAllUpProperties
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingReduction
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExchangePSD
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Tasaki 11.5.3: the half-filling ground energy is `0` (Theorem 11.26 PR3g)

On the half-filling sector `Ĥ_tJ = J · tJExchange` with `tJExchange ≥ 0`, and the all-up state is
annihilated, so the ground energy is exactly `0`:

* `tJ_groundEnergyAtFilling_eq_zero` — `groundEnergyAtFilling Ĥ_tJ (N+1) = 0`.

`≤ 0` from the all-up eigenvector at `0`; `≥ 0` from positive-semidefiniteness of `tJExchange`
(`J > 0`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- **The half-filling ground energy is `0`.**  `groundEnergyAtFilling Ĥ_tJ (N+1) = 0`: the all-up
state (annihilated by `Ĥ_tJ`) achieves `0`, and `Ĥ_tJ = J · tJExchange ≥ 0` on the sector. -/
theorem tJ_groundEnergyAtFilling_eq_zero (τ J : ℝ) (hJ : 0 < J) :
    groundEnergyAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1) = 0 := by
  refine le_antisymm ?_ ?_
  · -- the all-up state is an eigenvector at `0`
    refine groundEnergyAtFilling_le_of_eigenvector _ (N + 1) (hubbardAllUpState_ne_zero N) 0
      (fermionTotalNumber_mulVec_allUpState N) (hubbardAllUpState_mem_hardcore N) ?_
    rw [tJHamiltonian_mulVec_allUpState_eq_zero, Complex.ofReal_zero, zero_smul]
  · -- `≥ 0` via positive-semidefiniteness
    haveI : Nonempty ↥(fillingHardcoreStates N (N + 1)) := by
      refine ⟨⟨(WithLp.equiv 2 _).symm (hubbardAllUpState N), ?_, ?_, ?_⟩⟩
      · rw [EuclideanSpace.norm_eq]
        have : ∀ i, ‖((WithLp.equiv 2 ((Fin (2 * N + 2) → Fin 2) → ℂ)).symm
            (hubbardAllUpState N)).ofLp i‖ ^ 2 =
            if i = (fun k : Fin (2 * N + 2) => if k.val % 2 = 0 then 1 else 0) then 1 else 0 := by
          intro i
          change ‖hubbardAllUpState N i‖ ^ 2 = _
          rw [hubbardAllUpState, basisVec]
          split <;> simp
        rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_ite_eq' Finset.univ
          (fun k : Fin (2 * N + 2) => if k.val % 2 = 0 then 1 else 0), if_pos (Finset.mem_univ _)]
        simp
      · exact fermionTotalNumber_mulVec_allUpState N
      · exact hubbardAllUpState_mem_hardcore N
    rw [groundEnergyAtFilling]
    refine le_ciInf (fun φ => ?_)
    set v : (Fin (2 * N + 2) → Fin 2) → ℂ :=
      (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)).ofLp with hv
    have hhc : v ∈ hubbardHardcoreSubspace N := φ.2.2.2
    have hN : (fermionTotalNumber (2 * N + 1)).mulVec v = ((N + 1 : ℕ) : ℂ) • v := φ.2.2.1
    rw [rayleighOnVec, tJHamiltonian_mulVec_eq_smul_tJExchange_of_filling _ τ J hhc hN,
      dotProduct_smul, smul_eq_mul, Complex.mul_re]
    have hz : (0 : ℂ) ≤ star v ⬝ᵥ (tJExchange N (cycleGraph (N + 1))).mulVec v :=
      (tJExchange_posSemidef (cycleGraph (N + 1))).dotProduct_mulVec_nonneg v
    rw [Complex.le_def] at hz
    simp only [Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im] at hz ⊢
    nlinarith [hz.1, hz.2, hJ.le]

end LatticeSystem.Fermion
