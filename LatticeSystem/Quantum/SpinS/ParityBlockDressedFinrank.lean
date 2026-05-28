import LatticeSystem.Quantum.SpinS.ParityBlockUnshiftedFinrank
import LatticeSystem.Quantum.SpinS.ParityBlockPerronFinrank
import LatticeSystem.Quantum.SpinS.DressedAxisSwapPFMatrix

/-!
# Un-shifted dressed `Ĥ'` real-form parity-block matrix eigenspace `finrank ≤ 1`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(f) bridge step 2: applies the generic shift correspondence
`eigenspace_smul_one_sub_finrank_eq` (#3826) to the parity-block setting.  The shifted
parity-block matrix's Perron eigenspace bound `finrank ≤ 1` (#3825) transfers to the un-shifted
**real-form** dressed `Ĥ'` parity-block submatrix at the corresponding eigenvalue `c − μ_S`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Module Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Matrix identity**: the shifted parity-block submatrix equals `c • 1 − dressed_re submatrix`.
Built from `submatrix` distributing over `sub` / `smul`, and `submatrix_one` (for the injective
`Subtype.val`). -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (lam D : ℂ) (c : ℝ) (p : ℕ) :
    shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p =
      c • (1 : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ) -
        (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1) := by
  ext σ τ
  rw [shiftedDressedAxisSwappedReMatrixOnParityBlock_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.submatrix_apply, smul_eq_mul]
  by_cases hστ : σ = τ
  · subst hστ
    rw [shiftedDressedAxisSwappedReMatrix_apply_diag, Matrix.one_apply_eq, mul_one]
  · rw [shiftedDressedAxisSwappedReMatrix_apply_off_diag _ _ _ _ _ _
          (fun h => hστ (Subtype.ext h)),
        Matrix.one_apply_ne hστ, mul_zero, zero_sub]

/-- **Un-shifted dressed `Ĥ'` real-form parity-block submatrix eigenspace `finrank ≤ 1`**: from
the Perron eigenspace bound on the shifted parity-block matrix (#3825), the un-shifted real-form
parity-block submatrix has `finrank ≤ 1` at the corresponding `c − μ_S` eigenvalue. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_eigenspace_finrank_le_one
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
      Module.finrank ℝ
        (End.eigenspace
          (Matrix.toLin'
            ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
              (fun σ : parityConfigS Λ N p => σ.1)
              (fun σ : parityConfigS Λ N p => σ.1))) ν) ≤ 1 := by
  obtain ⟨μ, hfinrank⟩ :=
    shiftedDressedAxisSwappedReMatrixOnParityBlock_perron_eigenspace_finrank_le_one
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
      hA_ne hB_ne h_intermediate p
  refine ⟨c - μ, ?_⟩
  have heq :=
    @shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub Λ _ _ N A J lam D c p
  rw [heq] at hfinrank
  rw [eigenspace_smul_one_sub_finrank_eq] at hfinrank
  exact hfinrank

end LatticeSystem.Quantum
