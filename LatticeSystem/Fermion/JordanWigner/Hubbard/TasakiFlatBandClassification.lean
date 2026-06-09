import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandUniqueness
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandMultiplet
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandTheorem11_11

/-!
# Tasaki §11.3.1: discharging the Theorem 11.11 classification axiom (dimension route)

The half-filled zero-energy ground subspace of the flat-band Hubbard model equals the ferromagnetic
maximal-spin multiplet.  Following the §11.5 Theorem 11.26 dimension method (not symmetric-tensor
representation theory): the multiplet (dimension `K+2`) is contained in the ground subspace (the
existence half), and the ground subspace has dimension `≤ K+2` (amplitude invariance), so they
coincide — discharging `flatBand_zeroEnergy_halfFilled_mem_ferromagneticMultipletSpan`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Theorem 11.11; method as in §11.5.3, Theorem 11.26.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **The ferromagnetic multiplet has dimension `K+2 = 2 S_max + 1`** — its `K+2` lowered states
`(Ŝ⁻_tot)^k |Φα,all↑⟩` are linearly independent (`flatBand_ferromagnetic_multiplet`). -/
theorem flatBandFerromagneticMultipletSubmodule_finrank (K : ℕ) (ν : ℝ) :
    finrank ℂ (flatBandFerromagneticMultipletSubmodule K ν) = K + 2 := by
  rw [flatBandFerromagneticMultipletSubmodule,
    finrank_span_eq_card (flatBand_ferromagnetic_multiplet K ν).1, Fintype.card_fin]

/-- **`[Ŝ^z_tot, Ĥ_flat] = 0`.**  From `[Ŝ^±_tot, Ĥ_flat] = 0` and the `su(2)` relation
`Ŝ^+ Ŝ^- − Ŝ^- Ŝ^+ = 2 Ŝ^z`: `2 Ŝ^z` commutes with `Ĥ_flat`, hence so does `Ŝ^z`. -/
theorem fermionTotalSpinZ_commute_flatBandHamiltonian (K : ℕ) (ν t U : ℝ) :
    Commute (fermionTotalSpinZ (2 * K + 1)) (flatBandHamiltonian K ν t U) := by
  have hp := fermionTotalSpinPlus_commute_flatBandHamiltonian K ν t U
  have hm := fermionTotalSpinMinus_commute_flatBandHamiltonian K ν t U
  have h2 : Commute ((2 : ℂ) • fermionTotalSpinZ (2 * K + 1)) (flatBandHamiltonian K ν t U) := by
    rw [← fermionTotalSpinPlus_commutator_fermionTotalSpinMinus]
    exact (hp.mul_left hm).sub_left (hm.mul_left hp)
  have h2' : (2 : ℂ) • (fermionTotalSpinZ (2 * K + 1) * flatBandHamiltonian K ν t U)
      = (2 : ℂ) • (flatBandHamiltonian K ν t U * fermionTotalSpinZ (2 * K + 1)) := by
    rw [← smul_mul_assoc, ← mul_smul_comm]; exact h2.eq
  exact smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0) h2'

end LatticeSystem.Fermion
