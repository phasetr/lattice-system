import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import LatticeSystem.Math.MatrixAnalysis.EigenvalueMonotone

/-!
# Tasaki Appendix A.2.3: monotonicity of the trace of the exponential (Corollary A.8)

Corollary of the eigenvalue monotonicity (Theorem A.7), "useful in quantum statistical
mechanics": if self-adjoint operators satisfy `Â ≤ B̂`, then
`Tr[e^Â] ≤ Tr[e^B̂]`  (Tasaki eq. (A.2.31)),
and more generally `Tr[f(Â)] ≤ Tr[f(B̂)]` for any non-decreasing `f : ℝ → ℝ` (eq. (A.2.32)).
The proof is immediate from Theorem A.7: with the eigenvalues ordered, `a_j ≤ b_j`, so
`Σ_j f(a_j) ≤ Σ_j f(b_j)` for monotone `f`, and `Tr[f(Â)] = Σ_j f(a_j)`.

We record the concrete `f = exp` form (eq. (A.2.31)) for finite complex matrices, **now proved
(axiom-free)**: the spectral mapping `Tr[e^A] = Σ_j e^{a_j}` follows from the spectral theorem
`A = U·diag(a)·U⋆` — the exponential commutes with the (continuous) conjugation automorphism
(`map_exp`), `exp(diag a) = diag(e^a)` (`Matrix.exp_diagonal`), and the trace is invariant under
unitary conjugation (`Matrix.trace_mul_cycle`); the comparison `Σ_j e^{a_j} ≤ Σ_j e^{b_j}` is
Theorem A.7 (`hermitian_eigenvalues₀_monotone`, **proved** via Courant–Fischer) plus the
monotonicity of `Real.exp`.  `Tr` of a self-adjoint matrix is real, so the comparison is of real
parts.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.2.3, Corollary A.8, eqs. (A.2.31)–(A.2.32), p. 468.
-/

namespace LatticeSystem.Math

open Matrix
open scoped MatrixOrder ComplexOrder

/-- **Spectral mapping for the trace of the matrix exponential.**  For a Hermitian matrix `A`,
`Tr[e^A] = Σ_i e^{λ_i}` over the (real) eigenvalues of `A`: writing `A = U·diag(λ)·U⋆`
(`Matrix.IsHermitian.spectral_theorem`), the exponential passes through the continuous conjugation
automorphism (`map_exp`), exponentiates the diagonal entrywise (`Matrix.exp_diagonal`), and the
trace drops the unitary conjugation (`Matrix.trace_mul_cycle`). -/
theorem trace_exp_eq_sum_exp_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (NormedSpace.exp A).trace = ∑ i, Complex.exp (hA.eigenvalues i) := by
  -- the eigenvector unitary, as an invertible matrix with inverse `star U`
  have hu : IsUnit (hA.eigenvectorUnitary : Matrix n n ℂ) :=
    IsUnit.of_mul_eq_one _ (Unitary.coe_mul_star_self hA.eigenvectorUnitary)
  have hinv : (star hA.eigenvectorUnitary : Matrix n n ℂ)
      = (hA.eigenvectorUnitary : Matrix n n ℂ)⁻¹ :=
    (Matrix.inv_eq_right_inv (Unitary.coe_mul_star_self _)).symm
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, hinv,
    Matrix.exp_conj _ _ hu, Matrix.exp_diagonal]
  rw [Matrix.trace_mul_cycle,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), one_mul,
    Matrix.trace_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.coe_exp, Function.comp_apply, ← Complex.exp_eq_exp_ℂ]
  rfl

/-- **Tasaki Corollary A.8 (trace of the exponential is monotone), PROVED.**  For Hermitian
matrices `A ≤ B` (the Loewner order), `Tr[e^A] ≤ Tr[e^B]` (Tasaki eq. (A.2.31)).  Immediate from
the eigenvalue monotonicity (Theorem A.7, `hermitian_eigenvalues₀_monotone`, proved via
Courant–Fischer) through the spectral mapping `Tr[e^A] = Σ_j e^{a_j}`
(`trace_exp_eq_sum_exp_eigenvalues`) and the monotonicity of `Real.exp`.  The general form
`Tr[f(A)] ≤ Tr[f(B)]` for non-decreasing `f` (eq. (A.2.32)) holds the same way. -/
theorem hermitian_trace_exp_monotone {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B) :
    (NormedSpace.exp A).trace.re ≤ (NormedSpace.exp B).trace.re := by
  rw [trace_exp_eq_sum_exp_eigenvalues hA, trace_exp_eq_sum_exp_eigenvalues hB,
    Complex.re_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Complex.exp_ofReal_re, Complex.exp_ofReal_re]
  exact Real.exp_le_exp.mpr (hermitian_eigenvalues₀_monotone hA hB hAB _)

end LatticeSystem.Math
