import LatticeSystem.Quantum.SpinS.AxisSwappedBlockMinEq
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergAxisSwapMinEigenvalue
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfStructural

/-!
# Spin-1/2 anisotropic `Ĥ` eigenspace `≤ 2` at the global min eigenvalue

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) IVT crossing argument.

Combines:
- `spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_truly_unconditional`
  (PR #3888, obligation (1) ≤ 2 at axis-swap block-min energy).
- `hermitianMinEigenvalue_axisSwapped_eq_min_block_mins` (PR #3969, block-min
  equality on axis-swapped).
- `hermitianMinEigenvalue_anisotropic_eq_axisSwapped` (PR #3968, axis-swap
  spectrum bridge).

Conclusion: for spin-1/2 anisotropic `Ĥ` at real `(J, λ, D)` satisfying the
obligation (1) hypotheses, `finrank (eigenspace Ĥ (hermitianMinEigenvalue Ĥ)) ≤ 2`.

This is the form needed by the obligation (2) IVT crossing argument: at the
crossing point's global min energy, the eigenspace has `≤ 2` eigenvectors,
contradicting the ≥ 3 from the reflection.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 anisotropic `Ĥ` eigenspace `≤ 2` at its global min**: combining the
PR #3888 bound at the axis-swap block-min energy with the energy-identification
bridges (PRs #3968 + #3969), `finrank (eigenspace Ĥ (hermitianMinEigenvalue Ĥ)) ≤ 2`. -/
theorem spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hlam_star : star lam = lam) (hD_star : star D = D) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J lam D 1))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := 1)
          hJ_star hlam_star hD_star) : ℝ) : ℂ)) ≤ 2 := by
  classical
  -- (i) Energy of PR #3888's bound: min(parity-0 block min, parity-1 block min) of axis-swap.
  -- (ii) Via PR #3969, this equals hermitianMinEigenvalue axisSwapped.
  -- (iii) Via PR #3968, this equals hermitianMinEigenvalue Ĥ.
  -- So the energies match; PR #3888's eigenspace bound transfers via congrArg + the matching.
  have h3888 := spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_truly_unconditional
    A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos hc_strict hA_ne hB_ne
  -- h3888 : finrank (eigenspace Ĥ (min(block-0, block-1))) ≤ 2.
  -- Convert min(block-0, block-1) to hermitianMinEigenvalue Ĥ via PR #3969 + PR #3968.
  have hblock_eq := hermitianMinEigenvalue_axisSwapped_eq_min_block_mins
    (Λ := Λ) (N := 1) hJim hlam hDim hJself
  -- hblock_eq : hermitianMinEigenvalue axisSwapped_full = min(block-0, block-1).
  have hswap_eq := AxisSwapUnitaryS.hermitianMinEigenvalue_anisotropic_eq_axisSwapped
    (Λ := Λ) (N := 1) (G := axisSwapUnitarySpinHalf) hJ_star hlam_star hD_star
  -- hswap_eq : hermitianMinEigenvalue Ĥ = hermitianMinEigenvalue axisSwapped.
  -- Chain: hermitianMinEigenvalue Ĥ = hermitianMinEigenvalue axisSwapped (via hswap_eq)
  --                                  = min(block-0, block-1) (via hblock_eq).
  -- But axisSwapped_full_isHermitian_im uses the same matrix as axisSwappedAnisotropicHeisenbergS_isHermitian_of_real.
  -- The hermitianMinEigenvalue values match by congruence on the Hermitian instance.
  -- Rewrite the eigenvalue in h3888 to hermitianMinEigenvalue Ĥ.
  have henergy_eq : (min (hermitianMinEigenvalue
        (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
          (Λ := Λ) (N := 1) hJim hlam hDim 0))
        (hermitianMinEigenvalue
          (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
            (Λ := Λ) (N := 1) hJim hlam hDim 1)) : ℝ) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := 1)
          hJ_star hlam_star hD_star) := by
    rw [← hblock_eq, ← hswap_eq]
  rw [henergy_eq] at h3888
  exact h3888

end LatticeSystem.Quantum
