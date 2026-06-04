import LatticeSystem.Math.ComplexVectorKernel
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Positive-semidefinite kernel lemmas for the energy quadratic form

Model-agnostic linear-algebra lemmas linking positive-semidefiniteness, the
(unnormalized) energy quadratic form `rayleighOnVec M v = (star v ⬝ᵥ M v).re`, and
matrix kernels.  These power any frustration-free / PSD-sum ground-state argument
(Tasaki §11.3.1, and the general flat-band theory of §11.3.4), so they live in
`Math/` rather than a model-specific file.

* `posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero`: a zero of the energy form on a
  PSD matrix is a kernel vector.
* `conjTranspose_mul_self_mulVec_eq_zero`: `Aᴴ A v = 0 ⇒ A v = 0`.
* `rayleighOnVec_real_smul`, `rayleighOnVec_sum`: the energy form is real-scalar
  homogeneous and additive over finite sums.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- For a positive-semidefinite `M`, a zero of the (unnormalized) energy quadratic
form is a kernel vector: `rayleighOnVec M v = 0 → M v = 0`. -/
theorem posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero {n : Type*} [Fintype n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) {v : n → ℂ}
    (h0 : rayleighOnVec M v = 0) : M.mulVec v = 0 := by
  apply (hM.dotProduct_mulVec_zero_iff v).mp
  have hnn := hM.dotProduct_mulVec_nonneg v
  apply Complex.ext
  · exact h0
  · simpa using ((Complex.le_def.mp hnn).2).symm

/-- `Aᴴ A v = 0 → A v = 0` (the vanishing of `‖A v‖²`). -/
theorem conjTranspose_mul_self_mulVec_eq_zero {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m n ℂ} {v : n → ℂ} (h : (Aᴴ * A).mulVec v = 0) : A.mulVec v = 0 := by
  apply complexVec_eq_zero_of_star_dotProduct
  rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, h, dotProduct_zero]

/-- The energy quadratic form is real-scalar homogeneous. -/
theorem rayleighOnVec_real_smul {n : Type*} [Fintype n] (t : ℝ) (M : Matrix n n ℂ)
    (v : n → ℂ) : rayleighOnVec ((t : ℂ) • M) v = t * rayleighOnVec M v := by
  unfold rayleighOnVec
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- The energy quadratic form is additive over a finite sum of matrices. -/
theorem rayleighOnVec_sum {n ι : Type*} [Fintype n] (s : Finset ι)
    (f : ι → Matrix n n ℂ) (v : n → ℂ) :
    rayleighOnVec (∑ i ∈ s, f i) v = ∑ i ∈ s, rayleighOnVec (f i) v := by
  induction s using Finset.cons_induction with
  | empty => simp [rayleighOnVec]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, rayleighOnVec_add_matrix, ih]

end LatticeSystem.Quantum
