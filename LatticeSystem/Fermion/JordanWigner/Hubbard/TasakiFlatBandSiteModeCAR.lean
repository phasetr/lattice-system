import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModeCreation

/-!
# Tasaki §11.3.1: site annihilation against a rotated mode creation (toward block ≤ 1)

The site annihilation `ĉ_{x,σ}` is the mode annihilation at the unit single-particle vector
`δ_x`, so its anticommutator with a rotated mode creation `Ĉ†_τ(w)` collapses (via the generic
single-particle CAR) to the single-particle value `w(x)` when the spins match:
`{ĉ_{x,σ}, Ĉ†_τ(w)} = (w(x) if σ = τ else 0) · 1`.  Specialising `w` to a `flatBandBasis` vector
gives the amplitude that the site annihilation peels off each rotated mode creation in an
occupation monomial.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- The site annihilation `ĉ_{x,σ}` is the mode annihilation at the unit vector `δ_x`. -/
theorem flatBandModeAnnihilation_single (K : ℕ) (σ : Fin 2) (x : Fin (2 * K + 2)) :
    flatBandModeAnnihilation K σ (Pi.single x 1)
      = fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) := by
  simp only [flatBandModeAnnihilation, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single x]
  · rw [Pi.single_eq_same, one_smul]
  · intro y _ hy
    rw [Pi.single_eq_of_ne hy, zero_smul]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- **`{ĉ_{x,σ}, Ĉ†_τ(w)} = (w(x) if σ = τ else 0) · 1`.**  The site annihilation against a rotated
mode creation: the generic single-particle CAR at `δ_x` collapses the overlap sum to `w(x)`. -/
theorem flatBand_siteAnnihilation_modeCreation_anticomm (K : ℕ) (σ τ : Fin 2)
    (w : Fin (2 * K + 2) → ℂ) (x : Fin (2 * K + 2)) :
    fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) *
        flatBandModeCreation K τ w
      + flatBandModeCreation K τ w *
        fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)
      = (if σ = τ then w x else 0) • (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2))) := by
  rw [← flatBandModeAnnihilation_single K σ x, flatBandMode_annihilation_creation_anticomm]
  congr 1
  by_cases hστ : σ = τ
  · rw [if_pos hστ, if_pos hστ]
    rw [Finset.sum_eq_single x]
    · rw [Pi.single_eq_same, one_mul]
    · intro y _ hy
      rw [Pi.single_eq_of_ne hy, zero_mul]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  · rw [if_neg hστ, if_neg hστ]

end LatticeSystem.Fermion
