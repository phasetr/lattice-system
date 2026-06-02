import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSCaseIIBoundaryMoveSets
import LatticeSystem.Math.HermitianMinEqOfShiftPF
import LatticeSystem.Quantum.SpinS.HermitianMinSimilarInvariance
import LatticeSystem.Quantum.SpinS.MatrixSimilaritySpectrum
import LatticeSystem.Quantum.SpinS.ParityBlockUnshiftedFinrank
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge

/-!
# Case (ii): parity-block PF/min bridge

Issue #412 (Tasaki §2.5 Theorem 2.4, Mattis--Nishimori).

This file converts the case-(ii) shifted parity-gauged real block matrix into
the bare axis-swapped complex parity-block PF/min callback.  The proof is the
parity-block analogue of `AnisotropicSectorPFAtMin`: Perron--Frobenius gives a
simple positive eigenspace for the shifted real matrix, the shift identifies the
unshifted eigenvalue, Collatz--Wielandt identifies it with the Hermitian
minimum, and the combined Marshall/parity gauge transfers the result to the
bare axis-swapped parity block.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Combined gauge similarity -/

omit [DecidableEq Λ] in
/-- The complex case-(ii) parity gauge is the complexification of the real
case-(ii) parity gauge. -/
theorem caseIIParityGaugeSign_eq_ofReal_real {p : ℕ} (σ : parityConfigS Λ N p) :
    caseIIParityGaugeSign σ = (caseIIParityGaugeSignReal σ : ℂ) := by
  unfold caseIIParityGaugeSign caseIIParityGaugeSignReal
  norm_num

omit [DecidableEq Λ] in
/-- The complexification of the real combined gauge diagonal is the diagonal
with complexified entries. -/
theorem caseIICombinedGaugeDiagonalOnParity_map_eq (A : Λ → Bool) (p : ℕ) :
    (caseIICombinedGaugeDiagonalOnParity (Λ := Λ) (N := N) A p).map ((↑) : ℝ → ℂ) =
      Matrix.diagonal
        (fun σ : parityConfigS Λ N p =>
          ((caseIICombinedGaugeSignOnParity A σ : ℝ) : ℂ)) := by
  ext σ τ
  by_cases hστ : σ = τ
  · subst τ
    simp [caseIICombinedGaugeDiagonalOnParity]
  · simp [caseIICombinedGaugeDiagonalOnParity, hστ]

/-- The complexification of the real combined gauge diagonal squares to the
identity. -/
theorem caseIICombinedGaugeDiagonalOnParity_map_mul_self (A : Λ → Bool) (p : ℕ) :
    (caseIICombinedGaugeDiagonalOnParity (Λ := Λ) (N := N) A p).map ((↑) : ℝ → ℂ) *
      (caseIICombinedGaugeDiagonalOnParity (Λ := Λ) (N := N) A p).map ((↑) : ℝ → ℂ) =
        1 := by
  rw [caseIICombinedGaugeDiagonalOnParity_map_eq]
  ext σ τ
  by_cases hστ : σ = τ
  · subst τ
    simp only [Matrix.mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [← Complex.ofReal_mul, caseIICombinedGaugeSignOnParity_mul_self]
    norm_num
  · simp [hστ]

/-- The complexification of the case-(ii) parity-gauged real block is similar
to the bare axis-swapped parity block by the combined parity/Marshall gauge. -/
theorem caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_map_eq_combinedGauge_conj_bare
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) {D : ℂ} (hDim : D.im = 0) (p : ℕ) :
    (caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p).map
        ((↑) : ℝ → ℂ) =
      (caseIICombinedGaugeDiagonalOnParity (Λ := Λ) (N := N) A p).map ((↑) : ℝ → ℂ) *
        (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1) *
        (caseIICombinedGaugeDiagonalOnParity (Λ := Λ) (N := N) A p).map ((↑) : ℝ → ℂ) := by
  ext σ τ
  rw [Matrix.map_apply, caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_apply,
    caseIICombinedGaugeDiagonalOnParity_map_eq,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hmap := congrFun
    (congrFun
      (dressedAxisSwappedAnisotropicHeisenbergSReMatrix_submatrix_map_eq
        (Λ := Λ) (N := N) A hJim hJself hlam hDim p) σ) τ
  have hmar := congrFun
    (congrFun
      (dressedAxisSwapped_submatrix_eq_marshall_conj_bare
        (Λ := Λ) (N := N) A J lam D p) σ) τ
  rw [Matrix.map_apply, Matrix.submatrix_apply, Matrix.submatrix_apply] at hmap
  rw [marshallDiagonalOnParity, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.submatrix_apply] at hmar
  push_cast
  rw [hmap, hmar]
  unfold caseIICombinedGaugeSignOnParity
  push_cast
  rw [marshallSignS_eq_ofReal_re A σ.1, marshallSignS_eq_ofReal_re A τ.1]
  simp [Complex.ofReal_re]
  ring_nf

/-! ## Fixed parity-block PF/min bridge -/

/-- A fixed case-(ii) parity block has a bare PF/min witness once its shifted
parity-gauged real matrix is non-negative, irreducible, and strictly shifted on
the diagonal. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_shifted_block
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJself : ∀ x, J x x = 0)
    {lam : ℂ} (hlam : lam.im = 0) {D : ℂ} (hDim : D.im = 0)
    {c : ℝ} (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (hB_nn : ∀ σ τ : parityConfigS Λ N p,
      0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ)
    (hIrred :
      (shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible) :
    ∃ ν : ℝ,
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1))) (ν : ℂ)) ≤ 1 ∧
        ν = hermitianMinEigenvalue
          (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
            (Λ := Λ) (N := N) hJim hlam hDim p) := by
  classical
  let M_real : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
    caseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N p
  let B_real : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
    shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p
  have hM_symm : M_real.IsSymm := by
    dsimp [M_real]
    exact caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
      (N := N) A hJim hlam hDim p
  have hB_eq : B_real =
      c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real := by
    rfl
  obtain ⟨r, v, _hr_pos, hv_pos, hBv⟩ :=
    LatticeSystem.Math.PerronFrobeniusMain.exists_positive_eigenvector_of_irreducible
      hIrred
  have hBv_shift :
      (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real).mulVec v =
        r • v := by
    simpa [B_real, M_real, hB_eq] using hBv
  have h_finrank_shifted_R :
      finrank ℝ ↥(End.eigenspace (Matrix.toLin' B_real) r) ≤ 1 :=
    LatticeSystem.Math.PerronFrobenius.eigenspace_finrank_le_one_of_pos_eigenvec
      hIrred hBv hv_pos
  have h_finrank_gauged_R :
      finrank ℝ ↥(End.eigenspace (Matrix.toLin' M_real) (c - r)) ≤ 1 := by
    rw [hB_eq] at h_finrank_shifted_R
    rw [eigenspace_smul_one_sub_finrank_eq] at h_finrank_shifted_R
    exact h_finrank_shifted_R
  have h_finrank_gauged_C :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (M_real.map ((↑) : ℝ → ℂ)))
        ((c - r : ℝ) : ℂ)) ≤ 1 :=
    matrix_complex_eigenspace_finrank_le_one_of_real M_real (c - r)
      h_finrank_gauged_R
  have h_similarity_finrank :=
    matrix_similar_eigenspace_finrank_eq
      (caseIICombinedGaugeDiagonalOnParity_map_mul_self (Λ := Λ) (N := N) A p)
      (caseIICombinedGaugeDiagonalOnParity_map_mul_self (Λ := Λ) (N := N) A p)
      (by
        simpa [M_real] using
          caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_map_eq_combinedGauge_conj_bare
            (Λ := Λ) (N := N) A hJim hJself hlam hDim p)
      (((c - r : ℝ) : ℂ))
  rw [h_similarity_finrank] at h_finrank_gauged_C
  have hB_nn_shift :
      ∀ i j,
        0 ≤ (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real) i j := by
    intro i j
    rw [← hB_eq]
    exact hB_nn i j
  have hB_symm :
      (c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) - M_real).IsSymm :=
    (Matrix.isSymm_one.smul c).sub hM_symm
  have h_min_gauged :
      hermitianMinEigenvalue
        (LatticeSystem.Math.CollatzWielandt.isHermitian_map_ofReal_of_isSymm hM_symm) =
        c - r :=
    LatticeSystem.Math.CollatzWielandt.hermitianMinEigenvalue_lift_eq_sub_pf
      hM_symm c hB_nn_shift hB_symm hBv_shift hv_pos
  have h_spectrum :
      spectrum ℝ
          ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
            (fun σ : parityConfigS Λ N p => σ.1)
            (fun σ : parityConfigS Λ N p => σ.1)) =
        spectrum ℝ (M_real.map ((↑) : ℝ → ℂ)) := by
    exact matrix_similar_spectrum_real_eq
      (caseIICombinedGaugeDiagonalOnParity_map_mul_self (Λ := Λ) (N := N) A p)
      (caseIICombinedGaugeDiagonalOnParity_map_mul_self (Λ := Λ) (N := N) A p)
      (by
        simpa [M_real] using
          caseIIParityGaugedAxisSwappedReMatrixOnParityBlock_map_eq_combinedGauge_conj_bare
            (Λ := Λ) (N := N) A hJim hJself hlam hDim p)
  have h_min_bare :
      hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) hJim hlam hDim p) =
        c - r := by
    have hmin_eq := hermitianMinEigenvalue_eq_of_spectrum_eq
      (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
        (Λ := Λ) (N := N) hJim hlam hDim p)
      (LatticeSystem.Math.CollatzWielandt.isHermitian_map_ofReal_of_isSymm hM_symm)
      h_spectrum
    linarith [hmin_eq, h_min_gauged]
  refine ⟨c - r, ?_, ?_⟩
  · simpa [h_min_bare] using h_finrank_gauged_C
  · exact h_min_bare.symm

/-! ## Raw-support consumers -/

/-- In the strict case-(ii) region, raw support classification and block
reachability supply the bare parity-block PF/min witness. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_raw_support
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hlam_gt : 1 < lam.re)
    {D : ℂ} (hDim : D.im = 0) (hDneg : D.re < 0)
    {c : ℝ} (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (hc_strict : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 < c)
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      parityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ') :
    ∃ ν : ℝ,
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1))) (ν : ℂ)) ≤ 1 ∧
        ν = hermitianMinEigenvalue
          (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
            (Λ := Λ) (N := N) hJim hlam hDim p) := by
  have hc_le : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ.1 σ.1 ≤ c :=
    fun σ => le_of_lt (hc_strict σ)
  have hB_nn : ∀ σ τ : parityConfigS Λ N p,
      0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p σ τ :=
    shiftedCaseIIParityGaugedBlock_nonneg_of_raw_support
      A hJim hJnn hJpos hJself hJsupp hlam hlb hlam_gt hDim hDneg p hc_le
  have hIrred :
      (shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsIrreducible :=
    shiftedCaseIIParityGaugedBlock_irreducible_of_raw_support
      A hJim hJnn hJpos hJself hJsupp hlam hlb hlam_gt hDim hDneg p hc_strict hreach_total
  exact axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_shifted_block
    (Λ := Λ) (N := N) A hJim hJself hlam hDim p hB_nn hIrred

/-- At the `D = 0` boundary, raw support classification and bond-only block
reachability supply the bare parity-block PF/min witness. -/
theorem axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_raw_support_D_zero
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0)
    (hJsupp : ∀ x y, ¬ (bipartiteCompleteGraphOf A).Adj x y → J x y = 0)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hlam_gt : 1 < lam.re)
    {c : ℝ} (p : ℕ) [Nonempty (parityConfigS Λ N p)]
    (hc_strict : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam 0 N σ.1 σ.1 < c)
    (hreach_total : ∀ σ' σ : parityConfigS Λ N p, σ' ≠ σ →
      bondParityReachableSOnBlock (bipartiteCompleteGraphOf A) σ σ') :
    ∃ ν : ℝ,
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam (0 : ℂ) N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1))) (ν : ℂ)) ≤ 1 ∧
        ν = hermitianMinEigenvalue
          (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
            (Λ := Λ) (N := N) (J := J) (lam := lam) (D := (0 : ℂ))
            hJim hlam (by norm_num) p) := by
  have hc_le : ∀ σ : parityConfigS Λ N p,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam 0 N σ.1 σ.1 ≤ c :=
    fun σ => le_of_lt (hc_strict σ)
  have hB_nn : ∀ σ τ : parityConfigS Λ N p,
      0 ≤ shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam 0 N c p σ τ :=
    shiftedCaseIIBlock_nonneg_of_raw_support_D_zero
      A hJim hJnn hJpos hJself hJsupp hlam hlb hlam_gt p hc_le
  have hIrred :
      (shiftedCaseIIParityGaugedAxisSwappedReMatrixOnParityBlock A J lam 0 N c p).IsIrreducible :=
    shiftedCaseIIBlock_irreducible_of_raw_support_D_zero
      A hJim hJnn hJpos hJself hJsupp hlam hlb hlam_gt p hc_strict hreach_total
  exact axisSwappedAnisotropicHeisenbergS_submatrix_pf_min_of_caseII_shifted_block
    (Λ := Λ) (N := N) (D := (0 : ℂ)) A hJim hJself hlam (by norm_num) p hB_nn hIrred

end LatticeSystem.Quantum
