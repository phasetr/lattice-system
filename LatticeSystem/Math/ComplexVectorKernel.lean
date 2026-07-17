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

/-- `star v ⬝ᵥ v = ∑ ‖v i‖²` as a real cast into `ℂ` (the self inner product is a
non-negative real). -/
theorem star_dotProduct_self_eq {n : Type*} [Fintype n] (v : n → ℂ) :
    star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  rw [dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]

/-- For a nonzero vector `v`, the squared norm `(star v ⬝ᵥ v).re = ∑ ‖v_i‖²` is strictly
positive. -/
theorem dotProduct_star_self_re_pos {n : Type*} [Fintype n] {v : n → ℂ} (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ v).re := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
  rw [Pi.zero_apply] at hi₀
  rw [star_dotProduct_self_eq, Complex.ofReal_re]
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
    ⟨i₀, Finset.mem_univ _, Complex.normSq_pos.mpr hi₀⟩

/-- The conjugated quadratic form `⟨v, Mᴴ M v⟩ = ‖M v‖²` is a non-negative real. -/
theorem star_dotProduct_conjTranspose_mul_mulVec_eq {n : Type*} [Fintype n]
    (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ (M.conjTranspose * M).mulVec v =
      ((∑ i, Complex.normSq ((M.mulVec v) i) : ℝ) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, dotProduct,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]

end LatticeSystem
