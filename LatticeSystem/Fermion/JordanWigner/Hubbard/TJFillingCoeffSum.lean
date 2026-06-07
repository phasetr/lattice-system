import LatticeSystem.Fermion.JordanWigner.Hubbard.TJRaiseCoeffSum
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingBasis

/-!
# Tasaki 11.5: coefficient sum of a filling expansion (Prop 11.24 E3b PR5b-3a)

The coefficient-sum functional on the full `N̂ = Ne` filling expansion:

* `coeffSum_tJFillingExpansion` — `coeffSum (tJFillingExpansion v) = Σ_s v_s` (each basis state
  contributes `1`);
* `coeffSum_fermionTotalSpinPlus_tJFillingExpansion` — `coeffSum (Ŝ⁺_tot (tJFillingExpansion v)) =
  Σ_s v_s · #↓(s)` (each raised basis state contributes `#↓(s)`, sign-free).

Together these give the recursion `coeffSum (Ŝ⁺ ψ) = d · coeffSum ψ` for a hard-core
`N̂_↓`-eigenvector `ψ` at `d` (both `Ŝ⁺` and `N̂_↓` produce the same weighted sum `Σ_s v_s #↓(s)`),
the multiplicative step driving the positivity of the iterated raising.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Coefficient sum of a filling expansion.**  `coeffSum (tJFillingExpansion v) = Σ_s v_s`. -/
theorem coeffSum_tJFillingExpansion (N Ne : ℕ) (v : TJFillingSector N Ne → ℂ) :
    ∑ c, tJFillingExpansion N Ne v c = ∑ s, v s := by
  unfold tJFillingExpansion
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, coeffSum_basisVec, mul_one]

/-- **Coefficient sum of the raised filling expansion** is `Σ_s v_s · #↓(s)`
(`coeffSum (Ŝ⁺_tot (tJFillingExpansion v))`). -/
theorem coeffSum_fermionTotalSpinPlus_tJFillingExpansion (N Ne : ℕ)
    (v : TJFillingSector N Ne → ℂ) :
    ∑ c, (fermionTotalSpinPlus N).mulVec (tJFillingExpansion N Ne v) c =
      ∑ s, v s * ((Finset.univ.filter (fun x => s.val x = 2)).card : ℂ) := by
  unfold tJFillingExpansion
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
    coeffSum_fermionTotalSpinPlus_tJConfigOf]

end LatticeSystem.Fermion
