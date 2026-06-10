import LatticeSystem.Math.RayleighPosSemidefKernel
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Towards the Courant–Fischer min–max principle and Weyl monotonicity (Issue #4338)

This file builds, from mathlib's Hermitian spectral theorem and the Loewner order, the ingredients
of Weyl eigenvalue monotonicity (Tasaki Theorem A.7), discharging
`hermitian_eigenvalues₀_monotone`.  See `.self-local/docs/courant-fischer-design.md`.

The first layer records the *pointwise Rayleigh monotonicity* of the (unnormalized) energy
quadratic form `rayleighOnVec M v = (star v ⬝ᵥ M v).re` under the Loewner order: `A ≤ B` is exactly
pointwise domination `rayleighOnVec A v ≤ rayleighOnVec B v`.  This is the comparison step that, fed
through the block/pigeonhole argument, yields Weyl monotonicity.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n]

/-- The (unnormalized) energy quadratic form is monotone in the Loewner order: if `A ≤ B` then
`rayleighOnVec A v ≤ rayleighOnVec B v` for every vector `v`.  This is the pointwise Rayleigh
monotonicity that powers the eigenvalue comparison of Tasaki Theorem A.7. -/
theorem rayleighOnVec_mono {A B : Matrix n n ℂ} (hAB : A ≤ B) (v : n → ℂ) :
    rayleighOnVec A v ≤ rayleighOnVec B v := by
  have hps : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have h0 : (0 : ℝ) ≤ rayleighOnVec (B - A) v :=
    (Complex.le_def.mp (hps.dotProduct_mulVec_nonneg v)).1
  have hsplit : rayleighOnVec (B - A) v = rayleighOnVec B v - rayleighOnVec A v := by
    have hBA : B - A = B + ((-1 : ℝ) : ℂ) • A := by
      push_cast
      rw [neg_one_smul, ← sub_eq_add_neg]
    rw [hBA, rayleighOnVec_add_matrix, rayleighOnVec_real_smul]
    ring
  linarith [hsplit ▸ h0]

end LatticeSystem.Quantum
