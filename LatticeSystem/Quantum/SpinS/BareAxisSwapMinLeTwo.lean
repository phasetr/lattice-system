import LatticeSystem.Quantum.SpinS.BlockMinLeTwo
import LatticeSystem.Quantum.SpinS.ParityBlockSubmatrixHermitian

/-!
# Bare `Ĥ'` eigenspace `finrank ℂ ≤ 2` at `min(per-block mins)` — specialisation

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(i.7): specialises (i.6) #3851 to the bare axis-swapped anisotropic Heisenberg Hamiltonian
`Ĥ'`. Given per-sector PF simplicity hypotheses `finrank ≤ 1` at the per-sector
Hermitian minimum eigenvalues, the bare full-eigenspace at `min(min_0, min_1)` has
`finrank ℂ ≤ 2`. Discharges the block-diag and commute hypotheses of (i.6) inline.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Bare `Ĥ'` eigenspace `finrank ℂ ≤ 2` at `min(per-block mins)`** under per-sector
PF simplicity at the Hermitian minimum eigenvalues. -/
theorem axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_two_at_min_block_mins
    {J : Λ → Λ → ℂ} {lam D : ℂ}
    (hJ : ∀ x y, (J x y).im = 0) (hlam : lam.im = 0) (hD : D.im = 0)
    (hJself : ∀ x, J x x = 0)
    [Nonempty (parityConfigS Λ N 0)] [Nonempty (parityConfigS Λ N 1)]
    (h0 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 0 => σ.1)
          (fun σ : parityConfigS Λ N 0 => σ.1)))
          ((hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 0) : ℂ))) ≤ 1)
    (h1 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        ((axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).submatrix
          (fun σ : parityConfigS Λ N 1 => σ.1)
          (fun σ : parityConfigS Λ N 1 => σ.1)))
          ((hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 1) : ℂ))) ≤ 1) :
    finrank ℂ (End.eigenspace (Matrix.toLin'
      (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N))
      ((min
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 0))
          (hermitianMinEigenvalue
            (axisSwappedAnisotropicHeisenbergS_submatrix_isHermitian_of_real
              (Λ := Λ) (N := N) hJ hlam hD 1)) : ℝ) : ℂ)) ≤ 2 := by
  refine matrix_eigenspace_finrank_le_two_at_min_block_mins ?_ ?_ _ _ h0 h1
  · -- Block-diag: cross-parity entries vanish.
    intro σ τ hne_par
    have hne : σ ≠ τ := fun h => hne_par (by rw [h])
    have hodd : Odd (magSumS σ + magSumS τ) := by
      rw [Nat.odd_iff]
      have h1 : magSumS σ % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have h2 : magSumS τ % 2 < 2 := Nat.mod_lt _ (by norm_num)
      omega
    exact axisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne hJself lam D hne hodd
  · -- Commute with magParityDiagS.
    exact axisSwappedAnisotropicHeisenbergS_commute_magParityDiagS hJself lam D

end LatticeSystem.Quantum
