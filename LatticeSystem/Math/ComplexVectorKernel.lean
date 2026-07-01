import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Vanishing of a complex vector from a zero self-inner-product

A model-agnostic linear-algebra lemma: a complex vector `v` with
`star v ⬝ᵥ v = 0` (i.e. `∑ ‖v_i‖² = 0`) is zero.  Used by the fermionic
ground-state arguments (Slater-state nonvanishing, `Aᴴ A v = 0 ⇒ A v = 0`); kept
in `Math/` so it is reusable across models (Tasaki, Mielke, …) without importing
model-specific files.
-/

namespace LatticeSystem

open Matrix

/-- A complex vector with `star v ⬝ᵥ v = 0` is zero (`∑ ‖v_i‖² = 0`). -/
theorem complexVec_eq_zero_of_star_dotProduct {n : Type*} [Fintype n] {v : n → ℂ}
    (h : star v ⬝ᵥ v = 0) : v = 0 := by
  have hsum : ∑ j, (Complex.normSq (v j) : ℝ) = 0 := by
    have hc : (∑ j, (Complex.normSq (v j) : ℂ)) = 0 := by
      rw [← h, dotProduct]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
    exact_mod_cast hc
  funext j
  have hj : Complex.normSq (v j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg _)).mp hsum j
      (Finset.mem_univ j)
  exact Complex.normSq_eq_zero.mp hj

/-- For a (rectangular) complex matrix `M`, `star (M *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ Mᴴ *ᵥ w`
(adjoint move across the dot product). -/
theorem star_mulVec_dotProduct {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    (v : n → ℂ) (w : m → ℂ) :
    star (M.mulVec v) ⬝ᵥ w = star v ⬝ᵥ M.conjTranspose.mulVec w := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

end LatticeSystem
