import LatticeSystem.Quantum.SpinS.ParityBlockPerronFinrank
import LatticeSystem.Quantum.SpinS.DressedAxisSwapBlockIrreducibleUnconditional
import LatticeSystem.Quantum.SpinS.DressedAxisSwapPFMatrix
import LatticeSystem.Quantum.SpinS.ParityBlockUnshiftedFinrank
import LatticeSystem.Quantum.SpinS.ParityBlockDressedFinrank

/-!
# Existence of a strictly positive PF eigenvector for the unshifted dressed-Ĥ' submatrix

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(j.1): from PF on the shifted parity-block matrix (`B = c·I − M` for `M = dressed_re.submatrix`),
the PF positive eigenvector `v > 0` with `B v = μ_PF v` is also a positive eigenvector of the
UN-shifted matrix `M`, at eigenvalue `ν = c − μ_PF`:

```
M v = ν v   with   ν := c − μ_PF.
```

This is the existence half of the identification `ν = hermitianMinEigenvalue M` (the remaining
half — that `ν ≤ every other eigenvalue` — requires Collatz-Wielandt's "PF eigenvalue = max
spectrum" characterization, which is deferred).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix LatticeSystem.Math.PerronFrobenius

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Existence of a strictly positive eigenvector for the unshifted dressed-`Ĥ'` parity-block
submatrix**, derived from PF on the shifted matrix. -/
theorem dressedAxisSwappedAnisotropicHeisenbergSReMatrixOnParityBlock_pos_eigenvector_exists_legacy
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
    ∃ (ν : ℝ) (v : parityConfigS Λ N p → ℝ),
      (∀ i, 0 < v i) ∧
      Matrix.mulVec
        ((dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
          (fun σ : parityConfigS Λ N p => σ.1)
          (fun σ : parityConfigS Λ N p => σ.1)) v = ν • v := by
  -- Hermitian + irreducible on the shifted parity-block matrix.
  have hSymm := shiftedDressedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
    (N := N) A hJim hlam hDim c p
  have hHerm :
      (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hSymm
  have hIrred := shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible
    A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
    hA_ne hB_ne h_intermediate p
  -- Apply PF to get μ_PF, v > 0 with shifted v = μ_PF v.
  obtain ⟨μ, v, hAv, _hvne, hv_pos⟩ := exists_pos_eigenvec_max hHerm hIrred
  -- Rewrite shifted = c • 1 - dressed_re.submatrix.
  have heq := @shiftedDressedAxisSwappedReMatrixOnParityBlock_eq_smul_one_sub
    Λ _ _ N A J lam D c p
  rw [heq] at hAv
  -- (c • 1 - dressed_re.submatrix) v = μ v  ⟺  dressed_re.submatrix v = (c - μ) v.
  refine ⟨c - μ, v, hv_pos, ?_⟩
  -- LHS = dressed_re.submatrix v. We want to show it equals (c - μ) v.
  -- From hAv: (c • 1 - dressed_re.submatrix) v = μ v.
  -- c v - dressed_re.submatrix v = μ v ⟹ dressed_re.submatrix v = c v - μ v = (c - μ) v.
  set M : Matrix (parityConfigS Λ N p) (parityConfigS Λ N p) ℝ :=
    (dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D N).submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1) with hM_def
  -- hAv : (c • 1 - M) *ᵥ v = μ • v
  -- Expand via Matrix.sub_mulVec and Matrix.smul_mulVec_assoc.
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hAv
  -- hAv : c • v - M *ᵥ v = μ • v
  -- Want: M *ᵥ v = (c - μ) • v.
  have heq2 : Matrix.mulVec M v = c • v - μ • v := by linear_combination -hAv
  rw [heq2, sub_smul]

end LatticeSystem.Quantum
