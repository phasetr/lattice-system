import LatticeSystem.Quantum.SpinS.DressedAxisSwapImZero
import LatticeSystem.Quantum.SpinS.ParityBlockDressedFinrank
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge

/-!
# Complex dressed parity-block submatrix eigenspace `finrank ≤ 1`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(f.3-finish) step 3: combines #3827 (real-form `finrank ℝ ≤ 1`) and #3828 (real-to-complex
eigenspace bridge) with the matrix identity `(dressed_re.submatrix valS valS).map ((↑) : ℝ → ℂ) =
dressed_complex.submatrix valS valS` (which holds because every entry of `dressed_complex` is
real under real coefficients, #3830).  Result: the **complex** dressed parity-block submatrix
has `finrank ℂ ≤ 1` at the corresponding eigenvalue.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Module Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Matrix identity**: the cast of the dressed real-form parity-block submatrix equals the
complex dressed parity-block submatrix, under im=0 hyps on `J`, `lam`, `D`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrix_submatrix_map_eq
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJim : ∀ x y, (J x y).im = 0)
    (hJself : ∀ x, J x x = 0) {lam : ℂ} (hlam : lam.im = 0)
    {D : ℂ} (hDim : D.im = 0) (p : ℕ) :
    ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1) (fun σ : parityConfigS Λ N p => σ.1)).map
      ((↑) : ℝ → ℂ) =
      (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1) (fun σ : parityConfigS Λ N p => σ.1) := by
  ext σ τ
  rw [Matrix.map_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix_apply]
  -- Goal: ((dressed_complex σ.1 τ.1).re : ℂ) = dressed_complex σ.1 τ.1
  exact (Complex.ofReal_re _).symm ▸
    (Complex.ext rfl
      (dressedAxisSwappedAnisotropicHeisenbergS_apply_im_zero
        A hJim hJself hlam hDim σ.1 τ.1).symm)

/-- **Complex dressed parity-block submatrix `finrank ℂ ≤ 1`**: combines #3827 (real-form
`finrank ℝ ≤ 1`) with #3828 (real-to-complex bridge) via the matrix identity above. -/
theorem complex_dressed_parity_block_submatrix_eigenspace_finrank_le_one
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (N + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (h_intermediate : ∀ τ : Λ → Fin (N + 1), ∀ x : Λ,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    ∃ ν : ℝ,
      Module.finrank ℂ
        (End.eigenspace (Matrix.toLin'
          ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
            (fun σ : parityConfigS Λ N p => σ.1)
            (fun σ : parityConfigS Λ N p => σ.1))) (ν : ℂ)) ≤ 1 := by
  obtain ⟨ν, h_re⟩ :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_eigenspace_finrank_le_one
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
      hA_ne hB_ne h_intermediate p
  refine ⟨ν, ?_⟩
  have hbridge := matrix_complex_eigenspace_finrank_le_one_of_real
    ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1)) ν h_re
  have heq := @dressedAxisSwappedAnisotropicHeisenbergSReMatrix_submatrix_map_eq
    Λ _ _ N A J hJim hJself lam hlam D hDim p
  rw [heq] at hbridge
  exact hbridge

end LatticeSystem.Quantum
