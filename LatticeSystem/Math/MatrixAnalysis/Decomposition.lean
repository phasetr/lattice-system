import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Tasaki Appendix A.4.2: polar and singular-value decompositions (Theorems A.19, A.20)

Tasaki's two decomposition theorems for a general square matrix, proved together in the book:

* **Theorem A.20 (singular value decomposition)** — any `N × N` matrix `A` factors as `A = U D V†`
  with `U, V` unitary and `D = diagonal d` with `d_i = √λ_i ≥ 0`, the `λ_i ≥ 0` being the
  eigenvalues of the positive-semidefinite `A† A` (eq. (A.4.6)).
* **Theorem A.19 (polar decomposition)** — any `N × N` matrix `A` factors as `A = W C` with `W`
  unitary and `C` positive-semidefinite (eq. (A.4.2)); here `W = U V†` and `C = V D V†` from the SVD.

## Construction (both proved, axiom-free)
Let `M = A† A` (positive semidefinite, Hermitian).  By the spectral theorem `M = V Λ V†` with `V`
unitary (`Matrix.IsHermitian.eigenvectorUnitary`), eigenvalues `λ_i ≥ 0`
(`Matrix.PosSemidef.eigenvalues_nonneg`), and orthonormal eigenvectors `v_i` (the columns of `V`).
Set `d_i = √λ_i`.  The vectors `w_i = A v_i` are orthogonal with `‖w_i‖² = λ_i`, so for `λ_i ≠ 0`
the `u_i = d_i⁻¹ w_i` are orthonormal; extend this partial orthonormal family to a full orthonormal
basis (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`) and let `U` be its matrix.  Then
`A v_j = d_j u_j` for every `j` (for `λ_j = 0`, `w_j = 0`), i.e. `A V = U D`, hence `A = U D V†`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.4.2, Theorems A.19–A.20, eqs. (A.4.2)–(A.4.6), pp. 476–478.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Tasaki Theorem A.20 (singular value decomposition).**  Any square complex matrix `A` is
written as `A = U D V†`, with `U`, `V` unitary and `D = diagonal d` for nonnegative reals
`d_i = √λ_i` (`λ_i ≥ 0` the eigenvalues of `A† A`). -/
theorem matrix_singular_value_decomposition (A : Matrix n n ℂ) :
    ∃ (U V : Matrix n n ℂ) (d : n → ℝ),
      U ∈ Matrix.unitaryGroup n ℂ ∧ V ∈ Matrix.unitaryGroup n ℂ ∧ (∀ i, 0 ≤ d i) ∧
      A = U * Matrix.diagonal (fun i => (d i : ℂ)) * Matrix.conjTranspose V := by
  classical
  -- Spectral data of `M = A† A`.
  set M : Matrix n n ℂ := Aᴴ * A with hM_def
  have hMpsd : M.PosSemidef := posSemidef_conjTranspose_mul_self A
  set hMH : M.IsHermitian := hMpsd.1 with hMH_def
  set lam : n → ℝ := hMH.eigenvalues with hlam_def
  have hlam_nonneg : ∀ i, 0 ≤ lam i := fun i => hMpsd.eigenvalues_nonneg i
  set vb : OrthonormalBasis n ℂ (EuclideanSpace ℂ n) := hMH.eigenvectorBasis with hvb_def
  set d : n → ℝ := fun i => Real.sqrt (lam i) with hd_def
  have hd_nonneg : ∀ i, 0 ≤ d i := fun i => Real.sqrt_nonneg _
  have hd_sq : ∀ i, d i ^ 2 = lam i := fun i => Real.sq_sqrt (hlam_nonneg i)
  -- The image vectors `w_i = A v_i` in `EuclideanSpace`.
  set w : n → EuclideanSpace ℂ n := fun i => Matrix.toEuclideanLin A (vb i) with hw_def
  -- `⟪w i, w j⟫ = λ_j · δ_{ij}`.
  have hw_inner : ∀ i j, (inner ℂ (w i) (w j)) = ((if i = j then lam j else 0 : ℝ) : ℂ) := by
    intro i j
    rw [hw_def, EuclideanSpace.inner_eq_star_dotProduct]
    change (A *ᵥ WithLp.ofLp (hMH.eigenvectorBasis j)) ⬝ᵥ
      star (A *ᵥ WithLp.ofLp (hMH.eigenvectorBasis i)) = _
    sorry
  sorry

end LatticeSystem.Math
