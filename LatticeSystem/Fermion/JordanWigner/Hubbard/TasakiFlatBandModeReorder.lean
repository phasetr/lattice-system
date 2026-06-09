import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModeMonomial
import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularAllUpAnnihilation

/-!
# Tasaki §11.3.1: mode-creation anticommutation and reordering

The mode creations all anticommute: `{Ĉ†_σ(w), Ĉ†_τ(w')} = 0` (from the spinful site
creation–creation anticommutation by bilinearity).  This is the algebraic input for reordering a
rotated Fock monomial into a canonical (sorted) order — used to turn the list-indexed spanning
family `flatBandModeMonomial` into an occupation-config-indexed basis.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **Generic mode creation–creation anticommutation** `{Ĉ†_σ(w), Ĉ†_τ(w')} = 0`.  The bilinear
double sum of the spinful site anticommutations `{ĉ†_{x,σ}, ĉ†_{y,τ}} = 0` (all zero) vanishes
termwise.  Specialises to `{â†,â†}`, `{b̂†,b̂†}`, `{â†,b̂†}` all `= 0`. -/
theorem flatBandMode_creation_creation_anticomm (K : ℕ) (σ τ : Fin 2)
    (w w' : Fin (2 * K + 2) → ℂ) :
    flatBandModeCreation K σ w * flatBandModeCreation K τ w'
      + flatBandModeCreation K τ w' * flatBandModeCreation K σ w = 0 := by
  have hkey : flatBandModeCreation K σ w * flatBandModeCreation K τ w'
      + flatBandModeCreation K τ w' * flatBandModeCreation K σ w
      = ∑ x, ∑ y, (w x * w' y) •
          (fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) *
              fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ)
            + fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ) *
              fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)) := by
    simp only [flatBandModeCreation, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm _ (w' y), smul_mul_assoc,
      mul_smul_comm, smul_smul, mul_comm (w' y), ← smul_add]
  rw [hkey]
  refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun y _ => ?_))
  rw [spinful_creation_creation_anticomm, smul_zero]

end LatticeSystem.Fermion
