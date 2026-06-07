import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundWeightFinrankRaise
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundSpinHalfFinrank

/-!
# Tasaki 11.5: every `Ŝ³` weight space of the ground subspace is ≤ 1-dimensional (Prop 11.24 E5b)

Iterating the weight-finrank steps (`Ŝ⁻` from above, `Ŝ⁺` from below) down to the `Ŝ³ = ½` block —
which is `≤ 1` by E3a — bounds **every** `Ŝ³` weight space of `G`:

* `tJ_ground_weight_finrank_le_one_pos` — `finrank (G ⊓ Ŝ³=½+k) ≤ 1` for `k : ℕ`;
* `tJ_ground_weight_finrank_le_one_neg` — `finrank (G ⊓ Ŝ³=−½−k) ≤ 1` for `k : ℕ`.

The half-integer weights `±½, ±3/2, …` exhaust the `Ŝ³` spectrum at odd filling, so this caps each
block by `1` — the remaining input to the degeneracy upper bound `finrank G ≤ Ne+1`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- Every `Ŝ³ = ½ + k` weight space of the ground subspace is `≤ 1`-dimensional. -/
theorem tJ_ground_weight_finrank_le_one_pos (hpos : 0 < N) (Ne : ℕ) (hNeLt : Ne < N + 1)
    (hodd : Odd Ne) (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) (k : ℕ) :
    finrank ℂ ↥(groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((1 / 2 + k : ℝ)) : ℂ)) ≤ 1 := by
  induction k with
  | zero =>
    have h := tJ_groundSubmodule_spinHalf_finrank_le_one hpos Ne hNeLt hodd τ J hτ hJ
    rwa [show (((1 / 2 + (0 : ℕ) : ℝ)) : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
  | succ k ih =>
    have hstep := tJ_ground_weight_finrank_le_succ N Ne (cycleGraph (N + 1)) τ J (1 / 2 + (k : ℝ))
      (by positivity)
    rw [show (((1 / 2 + ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ) = (((1 / 2 + (k : ℝ)) + 1 : ℝ) : ℂ) by
      push_cast; ring]
    exact le_trans hstep ih

/-- Every `Ŝ³ = −½ − k` weight space of the ground subspace is `≤ 1`-dimensional. -/
theorem tJ_ground_weight_finrank_le_one_neg (hpos : 0 < N) (Ne : ℕ) (hNeLt : Ne < N + 1)
    (hodd : Odd Ne) (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) (k : ℕ) :
    finrank ℂ ↥(groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin (((-(1 / 2) - k : ℝ)) : ℂ)) ≤ 1 := by
  induction k with
  | zero =>
    rw [show (((-(1 / 2) - ((0 : ℕ) : ℝ)) : ℝ) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring]
    have hstep := tJ_ground_weight_finrank_le_of_spinZ_neg N Ne (cycleGraph (N + 1)) τ J
      (-(1 / 2)) (by norm_num)
    refine le_trans hstep ?_
    rw [show (((-(1 / 2) + 1 : ℝ)) : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    exact tJ_groundSubmodule_spinHalf_finrank_le_one hpos Ne hNeLt hodd τ J hτ hJ
  | succ k ih =>
    have hstep := tJ_ground_weight_finrank_le_of_spinZ_neg N Ne (cycleGraph (N + 1)) τ J
      (-(1 / 2) - ((k + 1 : ℕ) : ℝ)) (by
        have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith)
    refine le_trans hstep ?_
    rw [show (((-(1 / 2) - ((k + 1 : ℕ) : ℝ)) + 1 : ℝ) : ℂ) = (((-(1 / 2) - (k : ℝ)) : ℝ) : ℂ) by
      push_cast; ring]
    exact ih

end LatticeSystem.Fermion
