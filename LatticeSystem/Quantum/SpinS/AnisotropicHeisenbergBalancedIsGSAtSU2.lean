import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergFullMinGeSectorMin

/-!
# Balanced sector IS the GS at `(1, 0)` from the strict gap

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) first-crossing argument.

Under the strict-gap axiom `E_M_balanced(λ, D) < E_M(λ, D)` for all `M ≠ M_balanced`
with non-empty sector, the balanced sector IS the GS at `(λ, D)`:
`E_M_balanced(λ, D) = hermitianMinEigenvalue Ĥ(λ, D)`.

Proof: PR #3989 gives an `M` with `E_M = global min`. PR #3984 gives
`global min ≤ E_balanced`. If `M ≠ balanced`, the strict gap gives
`E_balanced < E_M = global min ≤ E_balanced`, contradiction. So `M = balanced`,
hence `E_balanced = global min`.

This brick is the key step that DISCHARGES the strict-GS axiom at `(1, 0)` of
PR #3986 (which #3985's `sSup ∈ set` needs for non-emptiness) from the
strict-gap axiom alone. Combined with the first-crossing scaffolding
(PRs #3982–#3986), the obligation (2) capstone's first-crossing axiom is
reduced to just the strict-gap axiom.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Balanced sector is the GS at `(λ, D)` from the strict gap**: under
`E_M_balanced(λ, D) < E_M(λ, D)` for all `M ≠ M_balanced` (with non-empty sector),
`hermitianMinEigenvalue Ĥ_M_balanced(λ, D) = hermitianMinEigenvalue Ĥ(λ, D)`. -/
theorem hermitianMinEigenvalue_balanced_eq_full_of_strict_gap
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    (N M_balanced : ℕ) (lam D : ℝ)
    [Nonempty (magConfigS Λ N M_balanced)] [Nonempty (Λ → Fin (N + 1))]
    (h_strict_gap :
      ∀ M : ℕ, ∀ _ : Nonempty (magConfigS Λ N M), M ≠ M_balanced →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ lam D) <
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M) hJ lam D)) :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ lam D) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N lam D) := by
  -- PR #3989: ∃ M non-empty with E_M ≤ global min.
  obtain ⟨M, hM_NE, hM_le⟩ :=
    exists_sector_hermitianMinEigenvalue_le_full (Λ := Λ) hJ N lam D
  -- PR #3984: global min ≤ E_balanced.
  have h_full_le_balanced :=
    hermitianMinEigenvalue_anisotropicHeisenbergS_full_le_sector
      (Λ := Λ) hJ N M_balanced lam D
  -- Case split on M = balanced or not.
  by_cases h_eq : M = M_balanced
  · -- M = balanced. E_balanced = E_M ≤ global min ≤ E_balanced, so equality.
    have : hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ lam D) ≤
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ N lam D) := by
      subst h_eq; exact hM_le
    exact le_antisymm this h_full_le_balanced
  · -- M ≠ balanced. Strict gap: E_balanced < E_M ≤ global min ≤ E_balanced. Contradiction.
    haveI := hM_NE
    have h_strict := h_strict_gap M hM_NE h_eq
    -- E_balanced < E_M ≤ global min ≤ E_balanced.
    exfalso
    linarith

end LatticeSystem.Quantum
