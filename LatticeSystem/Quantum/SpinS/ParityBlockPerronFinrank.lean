import LatticeSystem.Quantum.SpinS.DressedAxisSwapBlockIrreducibleUnconditional
import LatticeSystem.Quantum.SpinS.DressedAxisSwapPFMatrix
import LatticeSystem.Math.PerronFrobeniusFinrank
import LatticeSystem.Math.PerronFrobenius

/-!
# Parity-block Perron eigenspace `finrank ≤ 1`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(f) step 1A: combine the unconditional parity-block matrix irreducibility (#3824) with the
real-symmetric (= Hermitian on ℝ) property of the shifted parity-block matrix and Mathlib's
Perron–Frobenius `exists_pos_eigenvec_max` + `eigenspace_finrank_le_one_of_pos_eigenvec` (#3779)
to conclude: the Perron eigenspace of the shifted parity-block matrix has `finrank ≤ 1`.

This is the per-parity-block half of the `finrank ≤ 2` count needed for §2.5 Theorem 2.4
obligation (1).  The complementary work (real ↔ complex eigenspace bridge + summing the two
parity blocks + transferring to `Ĥ` via the gauge equivalence #3753) is the rest of (f) and (g).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Module Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Parity-block Perron eigenspace `finrank ≤ 1`**: under case (i.2) strict (plus the
intermediate-site and sublattice non-emptyness hypotheses needed by `parityReachableS_total`),
the Perron eigenspace of the shifted parity-block PF matrix is at most one-dimensional. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_perron_eigenspace_finrank_le_one
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
    ∃ μ : ℝ,
      Module.finrank ℝ
        (End.eigenspace
          (Matrix.toLin'
            (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p)) μ) ≤ 1 := by
  -- Hermitian from symmetric (real entries).
  have hSymm := shiftedDressedAxisSwappedReMatrixOnParityBlock_isSymm_of_real
    (N := N) A hJim hlam hDim c p
  have hHerm :
      (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hSymm
  -- Irreducibility unconditional via #3824.
  have hIrred := shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible
    A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict
    hA_ne hB_ne h_intermediate p
  -- Perron positive eigenvector + finrank ≤ 1 (#3779).
  obtain ⟨μ, v, hAv, _hvne, hv_pos⟩ :=
    LatticeSystem.Math.PerronFrobenius.exists_pos_eigenvec_max hHerm hIrred
  exact ⟨μ, LatticeSystem.Math.PerronFrobenius.eigenspace_finrank_le_one_of_pos_eigenvec
    hIrred hAv hv_pos⟩

end LatticeSystem.Quantum
