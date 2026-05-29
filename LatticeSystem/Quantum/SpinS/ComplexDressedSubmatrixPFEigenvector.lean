import LatticeSystem.Quantum.SpinS.DressedSubmatrixPFEigenvector
import LatticeSystem.Quantum.SpinS.ComplexDressedParityBlockFinrank
import LatticeSystem.Quantum.SpinS.SubmatrixMinEigenvalue

/-!
# Existence of complex PF eigenvector for the (complex) dressed-Ĥ' submatrix

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(j.2): lifts (j.1) #3857 (positive real eigenvector for the real-form dressed submatrix)
to the complex form via `Complex.ofReal`. Uses the matrix identity
`(dressed_re.submatrix).map ((↑) : ℝ → ℂ) = dressed_complex.submatrix` (#3831).

Then derives the one-direction bound `hermitianMinEigenvalue submatrix_Herm ≤ ν`
(where ν is the PF eigenvalue from (j.1)) using the spectrum-eigenvalues bridge
(`spectrum_real_eq_range_eigenvalues` + `hasEigenvalue_iff_mem_spectrum`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Lift the PF eigenvector to the complex dressed submatrix**: from (j.1) #3857, the
real-form dressed submatrix has a positive eigenvector `v : parityConfigS → ℝ` at `ν : ℝ`.
The complex lift `Complex.ofReal ∘ v` is then an eigenvector of the complex dressed
submatrix at `(ν : ℂ)`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_submatrix_complex_eigenvector_exists
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
    ∃ (ν : ℝ) (w : parityConfigS Λ N p → ℂ),
      w ≠ 0 ∧
      Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)) w = (ν : ℂ) • w := by
  -- (j.1): get positive real eigenvector.
  obtain ⟨ν, v, hv_pos, hvEq⟩ :=
    dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_pos_eigenvector_exists
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
      hA_ne hB_ne h_intermediate p
  refine ⟨ν, fun i => (v i : ℂ), ?_, ?_⟩
  · -- v.map ofReal ≠ 0: since v > 0, in particular v(any i) > 0, hence (v(i) : ℂ) ≠ 0.
    intro hzero
    obtain ⟨i⟩ : Nonempty (parityConfigS Λ N p) := inferInstance
    have hvi := congrFun hzero i
    simp only [Complex.ofReal_eq_zero, Pi.zero_apply] at hvi
    exact (hv_pos i).ne' hvi
  · -- The eigen-equation lifts.
    -- (dressed_re.submatrix).map ofReal = dressed_complex.submatrix (#3831 matrix identity).
    have hmap := @dressedAxisSwappedAnisotropicHeisenbergSReMatrix_submatrix_map_eq
      Λ _ _ N A J hJim hJself lam hlam D hDim p
    -- Apply mulVec to the lift.
    funext i
    show Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)) (fun i => (v i : ℂ)) i =
      ((ν : ℂ) • (fun i : parityConfigS Λ N p => (v i : ℂ))) i
    rw [← hmap]
    -- Now LHS uses the mapped matrix, which equals the lift of the real one's mulVec.
    set Mr : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
      (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1) with hMr_def
    have h_map_mulVec :
        Matrix.mulVec (Mr.map ((↑) : ℝ → ℂ)) (fun i => (v i : ℂ)) i =
        ((Mr.mulVec v i : ℝ) : ℂ) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl ?_
      intros j _
      simp [Complex.ofReal_mul]
    rw [h_map_mulVec]
    rw [show Mr.mulVec v i = (ν • v) i from congrFun hvEq i]
    simp [Complex.ofReal_mul]

end LatticeSystem.Quantum
