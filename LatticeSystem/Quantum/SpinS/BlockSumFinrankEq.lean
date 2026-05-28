import LatticeSystem.Quantum.SpinS.BlockDiagSubmatrixEmbed
import LatticeSystem.Quantum.SpinS.InvolutionEigenspaceDecompEq
import LatticeSystem.Quantum.SpinS.DressedAxisSwapDegeneracyBound

/-!
# Block-sum finrank equality: `finrank ℂ (eig M μ) = ∑_p finrank ℂ (eig M.submatrix_p μ)`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(h.3): combines (h.1) #3840 (per-block submatrix-full intersection finrank equality)
with (h.2) #3841 (involution decomposition finrank equality) to give the **block-sum
equality** for any parity-block-diagonal Hamiltonian commuting with `magParityDiagS`:
```
finrank ℂ (eig M μ) = finrank ℂ (eig M.submatrix_0 μ) + finrank ℂ (eig M.submatrix_1 μ)
```

Specialised to the dressed `Ĥ'_dressed` and the bare `Ĥ'` (both block-diagonal and
commuting with `P`), this gives the sharp `≤ 2` bound at any eigenvalue where the
two per-sector contributions are simultaneously ≤ 1 — the input for the
unconditional ground-state degeneracy bound via spectral minimisation
(deferred to subsequent work).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Block-sum finrank equality** for any complex matrix `M` that (i) is parity-block-diagonal
and (ii) commutes with `magParityDiagS`: at any `μ : ℂ`,
```
finrank ℂ (eig M μ) = finrank ℂ (eig M.submatrix_0 μ) + finrank ℂ (eig M.submatrix_1 μ)
```
Combines (h.1) #3840 (per-block submatrix-full intersection finrank equality) with
(h.2) #3841 (involution decomposition finrank equality). -/
theorem matrix_eigenspace_finrank_eq_sum_parity_blocks
    {M : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ}
    (hM_block : ∀ σ τ : Λ → Fin (N + 1), magSumS σ % 2 ≠ magSumS τ % 2 → M σ τ = 0)
    (hM_comm : M * magParityDiagS Λ N = magParityDiagS Λ N * M)
    (μ : ℂ) :
    finrank ℂ (End.eigenspace (Matrix.toLin' M) μ) =
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (M.submatrix
            (fun σ : parityConfigS Λ N 0 => σ.1)
            (fun σ : parityConfigS Λ N 0 => σ.1))) μ) +
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (M.submatrix
            (fun σ : parityConfigS Λ N 1 => σ.1)
            (fun σ : parityConfigS Λ N 1 => σ.1))) μ) := by
  -- Step 1: involution decomposition gives full eig = sum of inter ⊓ ker P_{±1}.
  have hsplit := eigenspace_finrank_eq_of_commuting_involution
    (Matrix.toLin' M) (Matrix.toLin' (magParityDiagS Λ N))
    (by rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hM_comm])
    (by rw [← Matrix.toLin'_mul, magParityDiagS_mul_self, Matrix.toLin'_one]) μ
  -- Step 2: per-block (h.1) equality replaces each inter ⊓ ker P_p with eig submatrix_p.
  have hp0 : (0 : ℕ) < 2 := by norm_num
  have hp1 : (1 : ℕ) < 2 := by norm_num
  have heq0 := parity_block_submatrix_full_inter_finrank_eq hM_block hp0 μ
  have heq1 := parity_block_submatrix_full_inter_finrank_eq hM_block hp1 μ
  -- ker(P=1) = eigenspace P 1 and (-1)^0 = 1; ker(P=-1) and (-1)^1 = -1.
  have hpow0 : ((-1 : ℂ) ^ 0) = 1 := by norm_num
  have hpow1 : ((-1 : ℂ) ^ 1) = -1 := by norm_num
  rw [hpow0] at heq0
  rw [hpow1] at heq1
  rw [hsplit, ← heq0, ← heq1]

/-- **Dressed `Ĥ'` block-sum finrank equality**: specialisation to the dressed
axis-swapped anisotropic Heisenberg. -/
theorem dressedAxisSwappedAnisotropicHeisenbergS_eigenspace_finrank_eq_sum_parity_blocks
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (dressedAxisSwappedAnisotropicHeisenbergS A J lam D N)) μ) =
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
            (fun σ : parityConfigS Λ N 0 => σ.1)
            (fun σ : parityConfigS Λ N 0 => σ.1))) μ) +
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          ((dressedAxisSwappedAnisotropicHeisenbergS A J lam D N).submatrix
            (fun σ : parityConfigS Λ N 1 => σ.1)
            (fun σ : parityConfigS Λ N 1 => σ.1))) μ) := by
  refine matrix_eigenspace_finrank_eq_sum_parity_blocks ?_ ?_ μ
  · intro σ τ hne_par
    have hne : σ ≠ τ := fun h => hne_par (by rw [h])
    have hodd : Odd (magSumS σ + magSumS τ) := by
      rw [Nat.odd_iff]
      have h1 : magSumS σ % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have h2 : magSumS τ % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    exact dressedAxisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne
      A hJself lam D hne hodd
  · exact dressedAxisSwappedAnisotropicHeisenbergS_commute_magParityDiagS A hJself lam D

/-- **Bare axis-swapped `Ĥ'` block-sum finrank equality**. -/
theorem axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_eq_sum_parity_blocks
    {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N)) μ) =
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          ((axisSwappedAnisotropicHeisenbergS J lam D N).submatrix
            (fun σ : parityConfigS Λ N 0 => σ.1)
            (fun σ : parityConfigS Λ N 0 => σ.1))) μ) +
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          ((axisSwappedAnisotropicHeisenbergS J lam D N).submatrix
            (fun σ : parityConfigS Λ N 1 => σ.1)
            (fun σ : parityConfigS Λ N 1 => σ.1))) μ) := by
  refine matrix_eigenspace_finrank_eq_sum_parity_blocks ?_ ?_ μ
  · intro σ τ hne_par
    have hne : σ ≠ τ := fun h => hne_par (by rw [h])
    have hodd : Odd (magSumS σ + magSumS τ) := by
      rw [Nat.odd_iff]
      have h1 : magSumS σ % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have h2 : magSumS τ % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    exact axisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne hJself lam D hne hodd
  · exact axisSwappedAnisotropicHeisenbergS_commute_magParityDiagS hJself lam D

end LatticeSystem.Quantum
