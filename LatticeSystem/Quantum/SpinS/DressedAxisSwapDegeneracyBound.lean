import LatticeSystem.Quantum.SpinS.BlockDiagSubmatrixBridge
import LatticeSystem.Quantum.SpinS.ComplexDressedParityBlockFinrank
import LatticeSystem.Quantum.SpinS.DressedAxisSwappedAnisotropic
import LatticeSystem.Quantum.SpinS.AxisSwapParityBlock
import LatticeSystem.Quantum.SpinS.MagParityEigenspaceDecomp

/-!
# Dressed `Ĥ'` eigenspace `finrank ≤ 2` via parity-block decomposition

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(g.1) bridge: combines

- (e) parity-block unconditional irreducibility (#3824),
- (f.bridge) shifted Perron `finrank ≤ 1` on parity-block submatrix (#3825–#3827),
- (f.3) real → complex eigenspace bridge (#3828),
- (f.3-finish) complex dressed parity-block submatrix `finrank ≤ 1` (#3829–#3831),
- (f.4) block-diag bridge full eigenspace ⊓ ker(P) → submatrix (#3832),

with the magnetization-parity involution decomposition (#3776) applied to the **dressed**
axis-swapped `Ĥ'_dressed`.

The dressed Hamiltonian (i) is parity-block-diagonal (inheriting from the bare via the
diagonal Marshall sign), and (ii) commutes with the magnetization-parity operator `P`
(diagonal × diagonal × diagonal — Θ_A commutes with P). Hence the same eigenspace split
applies; combined with the per-parity-block Perron simplicity from the chain above, the
global dressed `Ĥ'_dressed` eigenspace has `finrank ℂ ≤ 2`.

Subsequent PRs apply the Marshall similarity (`...finrank_eq`) and the axis-swap unitary
to lift this bound to the bare `Ĥ'` and ultimately to the original anisotropic `Ĥ`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Dressed `Ĥ'` is parity-block-diagonal**: cross-parity entries vanish.  Direct from the
bare block-diagonality (#3776 family) since `dressed σ τ = m(σ) m(τ) * bare σ τ`. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D : ℂ)
    {σ' σ : Λ → Fin (N + 1)} (hne : σ' ≠ σ)
    (hpar : Odd (magSumS σ' + magSumS σ)) :
    dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ' σ = 0 := by
  rw [dressedAxisSwappedAnisotropicHeisenbergS_apply,
      axisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne hJself lam D hne hpar,
      mul_zero]

/-- **Dressed `Ĥ'` commutes with the magnetization-parity operator**: entrywise as for the
bare case, using dressed parity-block diagonality. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_commute_magParityDiagS
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D : ℂ) :
    dressedAxisSwappedAnisotropicHeisenbergS A J lam D N * magParityDiagS Λ N =
      magParityDiagS Λ N * dressedAxisSwappedAnisotropicHeisenbergS A J lam D N := by
  ext σ' σ
  rw [magParityDiagS, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hσ : σ' = σ
  · rw [hσ]; ring
  · by_cases hpar : magSumS σ' % 2 = magSumS σ % 2
    · rw [mul_comm ((-1 : ℂ) ^ magSumS σ')
            (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N σ' σ)]
      congr 1
      rcases Nat.even_or_odd (magSumS σ) with he | ho
      · rw [Even.neg_one_pow he, Even.neg_one_pow (by rw [Nat.even_iff] at he ⊢; omega)]
      · rw [Odd.neg_one_pow ho, Odd.neg_one_pow (by rw [Nat.odd_iff] at ho ⊢; omega)]
    · rw [dressedAxisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne
            A hJself lam D hσ (by rw [Nat.odd_iff]; omega)]
      ring

/-- **Eigenspace finrank of dressed `Ĥ'` splits across the magnetization-parity blocks**.
Adapts `axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_parity_blocks` to the dressed
variant via the dressed commute lemma. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_parity_blocks
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N)) μ) ≤
      finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N)) μ ⊓
        End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) 1) +
      finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N)) μ ⊓
        End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) (-1)) := by
  refine eigenspace_finrank_le_of_commuting_involution _ _ ?_ ?_ μ
  · rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
        dressedAxisSwappedAnisotropicHeisenbergS_commute_magParityDiagS A hJself lam D]
  · rw [← Matrix.toLin'_mul, magParityDiagS_mul_self, Matrix.toLin'_one]

/-- **`≤ 2` degeneracy of dressed `Ĥ'` from per-parity-block simplicity**. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_two_of_blocks_le_one
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ)
    (heven : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N)) μ ⊓
      End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) 1) ≤ 1)
    (hodd : finrank ℂ ↥(End.eigenspace
        (Matrix.toLin' (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N)) μ ⊓
      End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) (-1)) ≤ 1) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N)) μ) ≤ 2 := by
  have hsplit :=
    dressedAxisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_parity_blocks
      (N := N) A hJself lam D μ
  omega

end LatticeSystem.Quantum
