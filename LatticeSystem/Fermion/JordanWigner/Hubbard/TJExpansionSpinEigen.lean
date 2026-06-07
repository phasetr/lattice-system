import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExpansion
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorSpin

/-!
# Tasaki 11.5: sector eigenvalues of the lifted ground vector (Prop 11.24 E3b PR5a)

A sector expansion `tJExpansion v = Σ_s v_s |Φ_s⟩` over the `Ŝ³ = ½`, `N̂ = Ne` sector is a joint
eigenvector of the diagonal charges:

* `fermionTotalSpinZ_mulVec_tJExpansion` — `Ŝ³ (tJExpansion v) = ½ (tJExpansion v)` (every sector
  state has `Ŝ³ = ½`);
* `fermionTotalDownNumber_mulVec_tJExpansion` — `N̂_↓ (tJExpansion v) = ((Ne−1)/2)(tJExpansion v)`
  (every sector state has `#↓ = (Ne−1)/2`).

These are the inputs that let `tJ_raised_highestWeight` apply to the lifted Perron–Frobenius ground
vector `Φ₀ = tJExpansion (ℂ ∘ v)` (`m = (Ne−1)/2`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- Every `Ŝ³ = ½`, `N̂ = Ne` sector state has exactly `(Ne−1)/2` down-spins. -/
theorem tJSpinHalfFillingSector_down_count (N Ne : ℕ) (s : TJSpinHalfFillingSector N Ne) :
    (Finset.univ.filter (fun k => s.val k = 2)).card = (Ne - 1) / 2 := by
  obtain ⟨hup, hsum⟩ := s.2
  omega

/-- **`Ŝ³` eigenvalue of a sector expansion.**  `Ŝ³ (tJExpansion v) = ½ (tJExpansion v)`. -/
theorem fermionTotalSpinZ_mulVec_tJExpansion (N Ne : ℕ) (v : TJSpinHalfFillingSector N Ne → ℂ) :
    (fermionTotalSpinZ N).mulVec (tJExpansion N Ne v) = ((1 / 2 : ℝ) : ℂ) • tJExpansion N Ne v := by
  unfold tJExpansion
  rw [Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mulVec_smul, fermionTotalSpinZ_mulVec_tJConfigOf_half N s.val s.2.1,
    smul_comm]

/-- **`N̂_↓` eigenvalue of a sector expansion** is `(Ne−1)/2`, as every sector state has that many
down-spins. -/
theorem fermionTotalDownNumber_mulVec_tJExpansion (N Ne : ℕ)
    (v : TJSpinHalfFillingSector N Ne → ℂ) :
    (fermionTotalDownNumber N).mulVec (tJExpansion N Ne v) =
      (((Ne - 1) / 2 : ℕ) : ℂ) • tJExpansion N Ne v := by
  unfold tJExpansion
  rw [Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mulVec_smul, fermionTotalDownNumber_mulVec_tJConfigOf]
  rw [tJSpinHalfFillingSector_down_count N Ne s, smul_comm]

end LatticeSystem.Fermion
