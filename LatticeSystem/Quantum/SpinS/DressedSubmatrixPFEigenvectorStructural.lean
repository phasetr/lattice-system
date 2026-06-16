import LatticeSystem.Quantum.SpinS.DressedAxisSwapBlockIrreducibleStructural
import LatticeSystem.Quantum.SpinS.ParityBlockPerronFinrank
import LatticeSystem.Quantum.SpinS.DressedAxisSwapPFMatrix
import LatticeSystem.Quantum.SpinS.ParityBlockUnshiftedFinrank
import LatticeSystem.Quantum.SpinS.ParityBlockDressedFinrank

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Structural (j.1) PF positive eigenvector (no `h_intermediate`)

Issue #3887 (Tasaki §2.5 Theorem 2.4, `h_intermediate` vacuous-at-N=1 fix).

(#3887.5): Structural variant of (j.1)
`dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_pos_eigenvector_exists_legacy`
that uses `shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible`
(#3887.4) instead of the h_intermediate-bearing original.

Drops `h_intermediate`; requires `hA_ne + hB_ne + 1 ≤ N`. Otherwise identical
conclusion + nearly-identical proof body.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix LatticeSystem.Math.PerronFrobenius

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **(#3887.5) (j.1) structural variant: PF positive eigenvector for the un-shifted
dressed-`Ĥ'` parity-block submatrix without `h_intermediate`**. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_pos_eigenvector_exists
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
    (hN : 1 ≤ N)
    (p : ℕ)
    [Nonempty (parityConfigS Λ N p)] :
    ∃ (ν : ℝ) (v : parityConfigS Λ N p → ℝ),
      (∀ i, 0 < v i) ∧
      Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)) v = ν • v := by
  have hSymm := shiftedDressedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
    (N := N) A hJim hlam hDim c p
  have hHerm :
      (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hSymm
  have hIrred := shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible
    A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
    hA_ne hB_ne hN p
  obtain ⟨μ, v, hAv, _hvne, hv_pos⟩ := exists_pos_eigenvec_max hHerm hIrred
  have heq := @shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
    Λ _ _ N A J lam D c p
  rw [heq] at hAv
  refine ⟨c - μ, v, hv_pos, ?_⟩
  set M : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1) with hM_def
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hAv
  have heq2 : Matrix.mulVec M v = c • v - μ • v := by linear_combination -hAv
  rw [heq2, sub_smul]

end LatticeSystem.Quantum
