import LatticeSystem.Quantum.SpinS.HermitianEigenspaceBotBelowMin
import LatticeSystem.Quantum.SpinS.BlockSumFinrankEq
import LatticeSystem.Quantum.SpinS.ParityBlockSubmatrixHermitian

/-!
# Block-diag eigenspace = ⊥ below joint per-block minimum

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(i.5): For a parity-block-diagonal matrix `M` commuting with `magParityDiagS`, if `μ`
is strictly less than the minimum eigenvalues of BOTH per-block submatrices, then the
full-eigenspace at `(μ : ℂ)` is `⊥`.

Combines (h.3) #3842 (block-sum finrank equality) with (i.4) #3849 (per-block
eigenspace = ⊥ below its min eigenvalue).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Block-diag eigenspace = ⊥ below joint per-block minimum** (generic): for `M`
parity-block-diagonal, commuting with `P`, with both `parityConfigS Λ N 0/1` non-empty,
and `μ : ℝ` strictly less than both per-block minimum eigenvalues, the full eigenspace
at `(μ : ℂ)` is `⊥`. -/
theorem matrix_eigenspace_eq_bot_of_real_lt_both_block_mins
    {M : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ}
    (hM_block : ∀ σ τ : Λ → Fin (N + 1), magSumS σ % 2 ≠ magSumS τ % 2 → M σ τ = 0)
    (hM_comm : M * magParityDiagS Λ N = magParityDiagS Λ N * M)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    (hM0_Herm : (M.submatrix
      (fun σ : parityConfigS Λ N 0 => σ.1)
      (fun σ : parityConfigS Λ N 0 => σ.1)).IsHermitian)
    (hM1_Herm : (M.submatrix
      (fun σ : parityConfigS Λ N 1 => σ.1)
      (fun σ : parityConfigS Λ N 1 => σ.1)).IsHermitian)
    {μ : ℝ}
    (h0 : μ < hermitianMinEigenvalue hM0_Herm)
    (h1 : μ < hermitianMinEigenvalue hM1_Herm) :
    End.eigenspace (Matrix.toLin' M) (μ : ℂ) = ⊥ := by
  -- Step 1: per-block eigenspaces = ⊥ below their respective min eigenvalues.
  have hb0 := hermitian_eigenspace_eq_bot_of_real_lt_min hM0_Herm h0
  have hb1 := hermitian_eigenspace_eq_bot_of_real_lt_min hM1_Herm h1
  -- Step 2: per-block finranks = 0 from eig = ⊥.
  have hf0 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (M.submatrix
        (fun σ : parityConfigS Λ N 0 => σ.1)
        (fun σ : parityConfigS Λ N 0 => σ.1))) (μ : ℂ)) = 0 := by
    rw [hb0]; exact finrank_bot ℂ _
  have hf1 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (M.submatrix
        (fun σ : parityConfigS Λ N 1 => σ.1)
        (fun σ : parityConfigS Λ N 1 => σ.1))) (μ : ℂ)) = 0 := by
    rw [hb1]; exact finrank_bot ℂ _
  -- Step 3: block-sum equality (h.3) gives full finrank = 0.
  have hsum := matrix_eigenspace_finrank_eq_sum_parity_blocks hM_block hM_comm (μ : ℂ)
  rw [hf0, hf1] at hsum
  -- Step 4: finrank = 0 ⟹ eigenspace = ⊥.
  exact Submodule.finrank_eq_zero.mp (by omega)

/-- **Bare `Ĥ'` eigenspace = ⊥ below joint per-block minimum** for real couplings. -/
theorem axisSwappedAnisotropicHeisenbergS_eigenspace_eq_bot_of_real_lt_both_block_mins
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0)
    (hJself : ∀ x, J x x = 0)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    {μ : ℝ}
    (h0 : μ < hermitianMinEigenvalue
      (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
        (Λ := Λ) (N := N) hJ hlam hD 0))
    (h1 : μ < hermitianMinEigenvalue
      (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
        (Λ := Λ) (N := N) hJ hlam hD 1)) :
    End.eigenspace (Matrix.toLin'
      (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N)) (μ : ℂ) = ⊥ := by
  refine matrix_eigenspace_eq_bot_of_real_lt_both_block_mins ?_ ?_ _ _ h0 h1
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
