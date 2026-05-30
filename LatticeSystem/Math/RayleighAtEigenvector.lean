import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.DotProduct

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Rayleigh quotient at an eigenvector

Issue #3871 (Tasaki §2.5 Theorem 2.4 PF identification chain).

(j.13.a): For a real matrix `M` and a real eigenvector `v` of `M` at eigenvalue `μ`
with `v ≠ 0`, the Rayleigh quotient `⟨v, Mv⟩ / ⟨v, v⟩` equals `μ`.

This is the most elementary step in the Collatz-Wielandt chain identifying the
Perron-Frobenius eigenvalue with the maximum Hermitian eigenvalue.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Math

open Matrix Finset

variable {n : Type*} [Fintype n]

/-- **Rayleigh quotient at an eigenvector equals the eigenvalue**.

For a real matrix `M` with a nonzero eigenvector `v` at eigenvalue `μ`:
`(∑ i, v i * (M *ᵥ v) i) / (∑ i, v i * v i) = μ`.

Proof: substitute `M *ᵥ v = μ • v`, then the numerator becomes `μ * ‖v‖²` and
the quotient evaluates to `μ`. -/
theorem rayleigh_quotient_at_eigenvector
    {M : Matrix n n ℝ} {μ : ℝ} {v : n → ℝ}
    (hv : M.mulVec v = μ • v) (hv_ne : v ≠ 0) :
    (∑ i, v i * (M.mulVec v) i) / (∑ i, v i * v i) = μ := by
  have h_denom_pos : 0 < ∑ i, v i * v i := by
    have h_nn : ∀ i ∈ univ, 0 ≤ v i * v i := fun i _ => mul_self_nonneg _
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv_ne
    exact sum_pos' h_nn ⟨i, mem_univ i, mul_self_pos.mpr hi⟩
  have h_denom_ne : (∑ i, v i * v i) ≠ 0 := ne_of_gt h_denom_pos
  have h_num : (∑ i, v i * (M.mulVec v) i) = μ * (∑ i, v i * v i) := by
    have : ∀ i, v i * (M.mulVec v) i = μ * (v i * v i) := fun i => by
      have := congrFun hv i
      simp [Pi.smul_apply, smul_eq_mul] at this
      rw [this]; ring
    rw [show (∑ i, v i * (M.mulVec v) i) = ∑ i, μ * (v i * v i) from
      Finset.sum_congr rfl (fun i _ => this i)]
    rw [← Finset.mul_sum]
  rw [h_num, mul_div_assoc, div_self h_denom_ne, mul_one]

end LatticeSystem.Math
