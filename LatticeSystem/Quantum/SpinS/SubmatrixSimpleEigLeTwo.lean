import LatticeSystem.Quantum.SpinS.BlockSumFinrankEq
import LatticeSystem.Quantum.SpinS.AxisSwapDegeneracy
import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySpinHalf

/-!
# `≤ 2` bound from per-submatrix-block simplicity (via (h.3))

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(h.4): wraps the (h.3) block-sum equality (#3842) into easier-to-use forms for
consumers of per-sector PF simplicity. The hypotheses are stated on the **submatrix**
eigenspaces (which is the form #3831/#3836 directly produce) rather than on the
intersected `eig ⊓ ker(P)` form (the conversion is via (h.1) #3840).

- Generic: any block-diagonal + commuting matrix with submatrix bounds ≤ 1 gives full ≤ 2.
- Dressed `Ĥ'`: same for `Ĥ'_dressed`.
- Bare `Ĥ'`: same for the axis-swapped Hamiltonian.
- Bare `Ĥ`: lifted via the axis-swap unitary (for `AxisSwapUnitaryS N` instances,
  and the spin-1/2 specialisation via `axisSwapUnitarySpinHalf`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Generic block-sum `≤ 2` from per-block submatrix simplicity**: if both parity-block
submatrices of a block-diagonal `M` (commuting with `magParityDiagS`) have `finrank ℂ ≤ 1`
at `μ`, then the full eigenspace has `finrank ℂ ≤ 2`. -/
theorem matrix_eigenspace_finrank_le_two_of_submatrix_blocks_le_one
    {M : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ}
    (hM_block : ∀ σ τ : Λ → Fin (N + 1), magSumS σ % 2 ≠ magSumS τ % 2 → M σ τ = 0)
    (hM_comm : M * magParityDiagS Λ N = magParityDiagS Λ N * M)
    (μ : ℂ)
    (h0 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (M.submatrix
          (fun σ : parityConfigS Λ N 0 => σ.1)
          (fun σ : parityConfigS Λ N 0 => σ.1))) μ) ≤ 1)
    (h1 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (M.submatrix
          (fun σ : parityConfigS Λ N 1 => σ.1)
          (fun σ : parityConfigS Λ N 1 => σ.1))) μ) ≤ 1) :
    finrank ℂ (End.eigenspace (Matrix.toLin' M) μ) ≤ 2 := by
  have hsum := matrix_eigenspace_finrank_eq_sum_parity_blocks hM_block hM_comm μ
  omega

/-- **Dressed `Ĥ'` block-sum `≤ 2`**: same for the dressed axis-swapped Hamiltonian. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_two_of_submatrix_blocks
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ)
    (h0 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
          (fun σ : parityConfigS Λ N 0 => σ.1)
          (fun σ : parityConfigS Λ N 0 => σ.1))) μ) ≤ 1)
    (h1 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
          (fun σ : parityConfigS Λ N 1 => σ.1)
          (fun σ : parityConfigS Λ N 1 => σ.1))) μ) ≤ 1) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N)) μ) ≤ 2 := by
  have hsum :=
    @dressedAxisSwappedAnisotropicHeisenbergS_eigenspace_finrank_eq_sum_parity_blocks
      Λ _ _ N A J hJself lam D μ
  omega

/-- **Bare `Ĥ'` block-sum `≤ 2`**: same for the bare axis-swapped Hamiltonian. -/
theorem axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_two_of_submatrix_blocks_le_one
    {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ)
    (h0 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 0 => σ.1)
          (fun σ : parityConfigS Λ N 0 => σ.1))) μ) ≤ 1)
    (h1 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 1 => σ.1)
          (fun σ : parityConfigS Λ N 1 => σ.1))) μ) ≤ 1) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 2 := by
  have hsum :=
    @axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_eq_sum_parity_blocks
      Λ _ _ N J hJself lam D μ
  omega

/-- **Bare anisotropic `Ĥ` block-sum `≤ 2`** via the axis-swap unitary `AxisSwapUnitaryS N`. -/
theorem anisotropicHeisenbergS_eigenspace_finrank_le_two_of_submatrix_blocks_le_one
    (G : AxisSwapUnitaryS N)
    {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ)
    (h0 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 0 => σ.1)
          (fun σ : parityConfigS Λ N 0 => σ.1))) μ) ≤ 1)
    (h1 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 1 => σ.1)
          (fun σ : parityConfigS Λ N 1 => σ.1))) μ) ≤ 1) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) ≤ 2 := by
  rw [← G.anisotropic_axisSwapped_eigenspace_finrank_eq J lam D μ]
  exact axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_two_of_submatrix_blocks_le_one
    hJself lam D μ h0 h1

/-- **Spin-1/2 instance** of the bare anisotropic `Ĥ` ≤ 2 from per-block submatrix simplicity. -/
theorem spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_of_submatrix_blocks_le_one
    {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ)
    (h0 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D 1).submatrix
          (fun σ : parityConfigS Λ 1 0 => σ.1)
          (fun σ : parityConfigS Λ 1 0 => σ.1))) μ) ≤ 1)
    (h1 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D 1).submatrix
          (fun σ : parityConfigS Λ 1 1 => σ.1)
          (fun σ : parityConfigS Λ 1 1 => σ.1))) μ) ≤ 1) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J lam D 1)) μ) ≤ 2 :=
  anisotropicHeisenbergS_eigenspace_finrank_le_two_of_submatrix_blocks_le_one
    axisSwapUnitarySpinHalf hJself lam D μ h0 h1

end LatticeSystem.Quantum
