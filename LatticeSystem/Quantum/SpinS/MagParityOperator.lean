import LatticeSystem.Quantum.SpinS.AxisSwapParityBlock

/-!
# The magnetization-parity operator and its commutation with `Ĥ'`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The diagonal operator `P = diag((−1)^{magSumS σ})` is an involution (`P² = 1`) with eigenvalues
`±1`.  By the parity block-diagonality of `Ĥ'` (#3772), `Ĥ'` **commutes** with `P` (for a coupling
without self-bonds), so the two `P`-eigenspaces (even/odd magnetization parity) are each
`Ĥ'`-invariant — the decomposition on which the parity-sector Perron–Frobenius degeneracy bound
runs (PR5).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The magnetization-parity operator `P = diag((−1)^{magSumS σ})`. -/
noncomputable def magParityDiagS (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    ManyBodyOpS Λ N :=
  Matrix.diagonal (fun σ => ((-1 : ℂ) ^ magSumS σ))

/-- The magnetization-parity operator is an involution: `P² = 1`. -/
theorem magParityDiagS_mul_self : magParityDiagS Λ N * magParityDiagS Λ N = 1 := by
  rw [magParityDiagS, Matrix.diagonal_mul_diagonal]
  rw [show (fun σ : Λ → Fin (N + 1) => ((-1 : ℂ) ^ magSumS σ) * ((-1 : ℂ) ^ magSumS σ)) =
      fun _ => 1 from
    funext fun σ => by rw [← pow_add]; exact Even.neg_one_pow ⟨magSumS σ, by ring⟩]
  exact Matrix.diagonal_one

/-- **`Ĥ'` commutes with the magnetization-parity operator** (no self-bonds). -/
theorem axisSwappedAnisotropicHeisenbergS_commute_magParityDiagS
    {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D : ℂ) :
    axisSwappedAnisotropicHeisenbergS J lam D N * magParityDiagS Λ N =
      magParityDiagS Λ N * axisSwappedAnisotropicHeisenbergS J lam D N := by
  ext σ' σ
  rw [magParityDiagS, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hσ : σ' = σ
  · rw [hσ]; ring
  · by_cases hpar : magSumS σ' % 2 = magSumS σ % 2
    · rw [mul_comm ((-1 : ℂ) ^ magSumS σ') (axisSwappedAnisotropicHeisenbergS J lam D N σ' σ)]
      congr 1
      rcases Nat.even_or_odd (magSumS σ) with he | ho
      · rw [Even.neg_one_pow he, Even.neg_one_pow (by rw [Nat.even_iff] at he ⊢; omega)]
      · rw [Odd.neg_one_pow ho, Odd.neg_one_pow (by rw [Nat.odd_iff] at ho ⊢; omega)]
    · rw [axisSwappedAnisotropicHeisenbergS_apply_eq_zero_of_magSum_parity_ne hJself lam D hσ
        (by rw [Nat.odd_iff]; omega)]
      ring

end LatticeSystem.Quantum
