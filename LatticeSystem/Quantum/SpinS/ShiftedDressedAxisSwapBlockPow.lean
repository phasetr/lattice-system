import LatticeSystem.Quantum.SpinS.ShiftedDressedAxisSwapBlockDiag

/-!
# Powers of the parity-block matrix restrict from the full shifted matrix

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Since the shifted dressed `Ĥ'` real-part matrix is block-diagonal in the magnetization parity
(#3788), every power of the parity-block submatrix agrees with the restriction of the
corresponding power of the full matrix:
`(blockMatrix ^ k) σ σ' = (fullMatrix ^ k) σ.1 σ'.1`.  This lets the parity-block reachability
matrix-power positivity (#3787, stated on the full matrix) descend to the parity-block submatrix,
the input to `Matrix.isIrreducible_iff_exists_pow_pos`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix Finset

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- A power of the parity-block matrix equals the restriction of the full matrix power. -/
theorem shiftedDressedAxisSwappedReMatrixOnParityBlock_pow_apply
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D : ℂ) (c : ℝ) (p : ℕ)
    (k : ℕ) (σ' σ : parityConfigS Λ N p) :
    (shiftedDressedAxisSwappedReMatrixOnParityBlock A J lam D N c p ^ k) σ' σ =
      (shiftedDressedAxisSwappedReMatrix A J lam D N c ^ k) σ'.1 σ.1 := by
  induction k generalizing σ' with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    rcases eq_or_ne σ' σ with h | h
    · simp [h]
    · rw [if_neg h, if_neg (fun hh => h (Subtype.ext hh))]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, pow_succ', Matrix.mul_apply]
    rw [Finset.sum_congr rfl (fun ρ _ => by
      rw [shiftedDressedAxisSwappedReMatrixOnParityBlock_apply, ih ρ])]
    rw [show (∑ ρ : parityConfigS Λ N p,
          shiftedDressedAxisSwappedReMatrix A J lam D N c σ'.1 ρ.1 *
            (shiftedDressedAxisSwappedReMatrix A J lam D N c ^ k) ρ.1 σ.1) =
        ∑ τ ∈ Finset.univ.filter (fun τ => magSumS τ % 2 = p),
          shiftedDressedAxisSwappedReMatrix A J lam D N c σ'.1 τ *
            (shiftedDressedAxisSwappedReMatrix A J lam D N c ^ k) τ σ.1 from
      (Finset.sum_subtype (Finset.univ.filter (fun τ => magSumS τ % 2 = p))
        (fun τ => by rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ τ, h⟩⟩)
        (fun τ => shiftedDressedAxisSwappedReMatrix A J lam D N c σ'.1 τ *
          (shiftedDressedAxisSwappedReMatrix A J lam D N c ^ k) τ σ.1)).symm]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro τ _ hτ
    rw [Finset.mem_filter, not_and] at hτ
    rw [shiftedDressedAxisSwappedReMatrix_apply_eq_zero_of_parity_ne A hJself lam D c
        (fun he => hτ (Finset.mem_univ τ) (by rw [← he, σ'.2])), zero_mul]

end LatticeSystem.Quantum
