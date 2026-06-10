import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.RCLike.Basic

/-!
# Tasaki Appendix A.4.2: polar and singular-value decompositions (Theorems A.19, A.20)

Tasaki's two decomposition theorems for a general square matrix, proved together in the book:

* **Theorem A.20 (singular value decomposition)** — any `N × N` matrix `A` factors as `A = U D V†`
  with `U, V` unitary and `D = diagonal d` with `d_i = √λ_i ≥ 0`, the `λ_i ≥ 0` being the
  eigenvalues of the positive-semidefinite `A† A` (eq. (A.4.6)).
* **Theorem A.19 (polar decomposition)** — any `N × N` matrix `A` factors as `A = W C` with `W`
  unitary and `C` positive-semidefinite (eq. (A.4.2)); here `W = U V†` and `C = V D V†` from
  the SVD.

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
    simp only [hw_def]
    rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    -- `Aᴴ.toEuclideanLin (A.toEuclideanLin (vb j)) = M.toEuclideanLin (vb j) = lam_j • vb j`
    have htel : (Matrix.toEuclideanLin Aᴴ) (Matrix.toEuclideanLin A (hMH.eigenvectorBasis j))
        = ((hMH.eigenvalues j : ℝ) : ℂ) • (hMH.eigenvectorBasis j : EuclideanSpace ℂ n) := by
      apply WithLp.ofLp_injective (p := 2) (V := n → ℂ)
      have hofLp : WithLp.ofLp ((Matrix.toEuclideanLin Aᴴ)
            (Matrix.toEuclideanLin A (hMH.eigenvectorBasis j)))
          = M *ᵥ WithLp.ofLp (hMH.eigenvectorBasis j) := by
        change Aᴴ *ᵥ (A *ᵥ WithLp.ofLp (hMH.eigenvectorBasis j))
          = M *ᵥ WithLp.ofLp (hMH.eigenvectorBasis j)
        rw [Matrix.mulVec_mulVec]
      rw [hofLp, hMH.mulVec_eigenvectorBasis j]
      funext k
      simp only [Pi.smul_apply, WithLp.ofLp_smul, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
      rfl
    rw [htel, inner_smul_right,
      orthonormal_iff_ite.mp hMH.eigenvectorBasis.orthonormal i j, hlam_def]
    split <;> simp
  -- Support of the spectrum; image vectors vanish off the support.
  set s : Set n := {i | lam i ≠ 0} with hs_def
  have hw_zero : ∀ i, lam i = 0 → w i = 0 := by
    intro i hi
    have h0 : inner ℂ (w i) (w i) = 0 := by rw [hw_inner]; simp [hi]
    exact inner_self_eq_zero.mp h0
  have hd_pos : ∀ i, i ∈ s → 0 < d i := fun i hi =>
    Real.sqrt_pos.mpr (lt_of_le_of_ne (hlam_nonneg i) (Ne.symm hi))
  -- Normalised image vectors `u_i = d_i⁻¹ w_i` (ℂ-smul), orthonormal on the support.
  set u : n → EuclideanSpace ℂ n := fun i => (((d i)⁻¹ : ℝ) : ℂ) • w i with hu_def
  have hu_ortho : Orthonormal ℂ (s.restrict u) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.restrict_apply, hu_def, inner_smul_left, inner_smul_right, hw_inner,
      Complex.conj_ofReal, Subtype.mk.injEq]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      have hdne : d i ≠ 0 := ne_of_gt (hd_pos i hi)
      have hr : ((d i)⁻¹ : ℝ) * ((d i)⁻¹ * lam i) = 1 := by
        rw [← hd_sq i]; field_simp
      rw [show ((((d i)⁻¹ : ℝ) : ℂ)) * (((((d i)⁻¹ : ℝ) : ℂ)) * ((lam i : ℝ) : ℂ))
          = ((((d i)⁻¹ : ℝ) * ((d i)⁻¹ * lam i) : ℝ) : ℂ) by push_cast; ring, hr]
      norm_num
    · rw [if_neg hij, if_neg hij]
      simp
  -- Extend to a full orthonormal basis; `U` is its matrix (unitary).
  obtain ⟨ub, hub⟩ := hu_ortho.exists_orthonormalBasis_extension_of_card_eq
    finrank_euclideanSpace
  set U : Matrix n n ℂ := (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix ub.toBasis with hU_def
  have hU_unit : U ∈ Matrix.unitaryGroup n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary ub
  have hU_mulVec : ∀ l, U *ᵥ Pi.single l 1 = ⇑(ub l) := by
    intro l; rw [Matrix.mulVec_single_one]; rfl
  set V : Matrix n n ℂ := (hMH.eigenvectorUnitary : Matrix n n ℂ) with hV_def
  have hV_unit : V ∈ Matrix.unitaryGroup n ℂ := hMH.eigenvectorUnitary.2
  -- Column identity `w_l = d_l • ub_l`.
  have hcol : ∀ l, w l = ((d l : ℝ) : ℂ) • (ub l : EuclideanSpace ℂ n) := by
    intro l
    by_cases hl : l ∈ s
    · rw [hub l hl]
      simp only [hu_def, smul_smul]
      rw [show ((d l : ℝ) : ℂ) * (((d l)⁻¹ : ℝ) : ℂ) = 1 by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (hd_pos l hl))]; norm_num, one_smul]
    · have hlam0 : lam l = 0 := by simpa [hs_def] using hl
      rw [hw_zero l hlam0]
      simp [hd_def, hlam0]
  -- `A V = U D` (columnwise), hence `A = U D Vᴴ`.
  have hcols : ∀ l, (A * V) *ᵥ Pi.single l 1
      = (U * Matrix.diagonal (fun i => (d i : ℂ))) *ᵥ Pi.single l 1 := by
    intro l
    have hsingle : (Pi.single l ((d l : ℂ)) : n → ℂ)
        = (d l : ℂ) • (Pi.single l (1 : ℂ) : n → ℂ) := by
      funext k; by_cases hk : k = l <;> simp [Pi.single_apply, hk]
    rw [← Matrix.mulVec_mulVec, hV_def, hMH.eigenvectorUnitary_mulVec l,
      ← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single, mul_one, hsingle,
      Matrix.mulVec_smul, hU_mulVec]
    have := congrArg WithLp.ofLp (hcol l)
    simpa using this
  have hAV : A * V = U * Matrix.diagonal (fun i => (d i : ℂ)) := by
    ext i l
    have hil := congrFun (hcols l) i
    simpa only [Matrix.mulVec_single_one] using hil
  have hVstar : V * Vᴴ = 1 := by
    have := hV_unit
    rw [Matrix.mem_unitaryGroup_iff] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨U, V, d, hU_unit, hV_unit, hd_nonneg, ?_⟩
  calc A = A * (V * Vᴴ) := by rw [hVstar, Matrix.mul_one]
    _ = (A * V) * Vᴴ := by rw [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i => (d i : ℂ)) * Vᴴ := by rw [hAV]

/-- **Tasaki Theorem A.19 (polar decomposition).**  Any square complex matrix `A` factors as
`A = W C` with `W` unitary and `C` positive-semidefinite.  Derived from the singular value
decomposition `A = U D V†` by `W = U V†`, `C = V D V†`. -/
theorem matrix_polar_decomposition (A : Matrix n n ℂ) :
    ∃ (W C : Matrix n n ℂ), W ∈ Matrix.unitaryGroup n ℂ ∧ C.PosSemidef ∧ A = W * C := by
  obtain ⟨U, V, d, hU, hV, hd, hA⟩ := matrix_singular_value_decomposition A
  have hDpsd : (Matrix.diagonal (fun i => (d i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (by intro i; simp only [Pi.zero_apply]; exact_mod_cast hd i)
  have hVstarV : Vᴴ * V = 1 := by
    have hv := hV
    rw [Matrix.mem_unitaryGroup_iff'] at hv
    simpa [Matrix.star_eq_conjTranspose] using hv
  have hVconj_mem : Vᴴ ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact hVstarV
  refine ⟨U * Vᴴ, V * Matrix.diagonal (fun i => (d i : ℂ)) * Vᴴ, mul_mem hU hVconj_mem,
    hDpsd.mul_mul_conjTranspose_same V, ?_⟩
  · rw [hA, show (U * Vᴴ) * (V * Matrix.diagonal (fun i => (d i : ℂ)) * Vᴴ)
        = U * (Vᴴ * V) * Matrix.diagonal (fun i => (d i : ℂ)) * Vᴴ by
      simp only [Matrix.mul_assoc], hVstarV, Matrix.mul_one]

end LatticeSystem.Math
