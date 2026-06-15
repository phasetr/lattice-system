import LatticeSystem.Quantum.SpinS.BlockEigBotBelowJointMin

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Full eigenspace `≤ 2` at the minimum of the per-block min eigenvalues

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(i.6): The final assembly step.  For a parity-block-diagonal `M` (commuting with `P`,
with both per-block submatrices Hermitian and `parityConfigS Λ N 0/1` non-empty),
given per-block bounds `finrank ≤ 1` at the **per-block minimum eigenvalues**,
the full-eigenspace at `min(min_0, min_1)` has `finrank ≤ 2`:

- If `min_0 = min_1`: both contribute `≤ 1`, total `≤ 2`.
- If `min_0 < min_1` (or vice-versa): the lower contributes `≤ 1`, the higher contributes
  `0` (by (i.5) #3850), total `≤ 1`.

This is the bridge from the per-block PF simplicity (PF gives `≤ 1` at the min) to the
unconditional global ground-state degeneracy `≤ 2`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Full eigenspace `≤ 2` at the minimum of per-block min eigenvalues** (generic). -/
theorem matrix_eigenspace_finrank_le_two_at_min_block_mins
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
    (h0 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (M.submatrix
          (fun σ : parityConfigS Λ N 0 => σ.1)
          (fun σ : parityConfigS Λ N 0 => σ.1)))
            ((hermitianMinEigenvalue hM0_Herm : ℂ))) ≤ 1)
    (h1 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (M.submatrix
          (fun σ : parityConfigS Λ N 1 => σ.1)
          (fun σ : parityConfigS Λ N 1 => σ.1)))
            ((hermitianMinEigenvalue hM1_Herm : ℂ))) ≤ 1) :
    finrank ℂ (End.eigenspace (Matrix.toLin' M)
      ((min (hermitianMinEigenvalue hM0_Herm) (hermitianMinEigenvalue hM1_Herm) : ℝ) : ℂ)) ≤ 2 := by
  set ν0 := hermitianMinEigenvalue hM0_Herm
  set ν1 := hermitianMinEigenvalue hM1_Herm
  set ν := min ν0 ν1
  -- Apply (h.3) at ν.
  have hsum := matrix_eigenspace_finrank_eq_sum_parity_blocks hM_block hM_comm (ν : ℂ)
  rw [hsum]
  -- Case analysis: ν = ν0 or ν = ν1 (and possibly both).
  by_cases hle_case : ν0 ≤ ν1
  · -- ν = ν0 ≤ ν1.
    have hν : ν = ν0 := min_eq_left hle_case
    rw [hν]
    -- finrank submatrix_0 at ν0 ≤ 1 (h0).
    -- For submatrix_1: if ν0 < ν1, then by (i.4), eig submatrix_1 ν0 = ⊥, so finrank = 0.
    --                  if ν0 = ν1, then h1 applies.
    rcases lt_or_eq_of_le hle_case with hlt' | heq
    · -- ν0 < ν1: submatrix_1 eig at ν0 = ⊥ ⟹ finrank = 0.
      have h_sub1 : End.eigenspace (Matrix.toLin'
          (M.submatrix
            (fun σ : parityConfigS Λ N 1 => σ.1)
            (fun σ : parityConfigS Λ N 1 => σ.1))) ((ν0 : ℂ)) = ⊥ :=
        hermitian_eigenspace_eq_bot_of_real_lt_min hM1_Herm hlt'
      rw [h_sub1, finrank_bot]
      omega
    · -- ν0 = ν1: both per-block bounds apply.
      rw [← heq] at h1
      omega
  · -- ν1 < ν0: ν = ν1.
    push Not at hle_case
    have hν : ν = ν1 := min_eq_right (le_of_lt hle_case)
    rw [hν]
    -- For submatrix_0: by (i.4), eig submatrix_0 ν1 = ⊥, so finrank = 0.
    have h_sub0 : End.eigenspace (Matrix.toLin'
        (M.submatrix
          (fun σ : parityConfigS Λ N 0 => σ.1)
          (fun σ : parityConfigS Λ N 0 => σ.1))) ((ν1 : ℂ)) = ⊥ :=
      hermitian_eigenspace_eq_bot_of_real_lt_min hM0_Herm hle_case
    rw [h_sub0, finrank_bot]
    omega

end LatticeSystem.Quantum
