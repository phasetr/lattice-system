/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.EqMagnetizationReachable

/-!
# The shifted dressed Heisenberg matrix `c·I − M` on `H_0`

To apply Perron–Frobenius (`Math.PerronFrobenius.exists_pos_eigenvec_max`),
we need a **non-negative** symmetric irreducible matrix.  The dressed
Heisenberg matrix `M = dressedHeisenbergMatrixH0 A J` is symmetric
with non-positive off-diagonal entries (PR α-5a), but its diagonal
entries are arbitrary real numbers.  Shifting by `c · I` for
sufficiently large `c` brings the matrix into the non-negative
regime suitable for PF: `B := c·I - M` then has

- **symmetric** (PR α-5a + scalar shift),
- **non-negative off-diagonal** (sign flip of `M`'s non-positive
  off-diagonal),
- **non-negative diagonal** when `c ≥ M σ σ` for all `σ`.

Note: shifting commutes with eigenvector structure — eigenvalue `μ`
of `M` corresponds to eigenvalue `c − μ` of `B` with the same
eigenvector. The maximum eigenvalue of `B` corresponds to the
**minimum** eigenvalue of `M`, i.e., the **ground state** of the
restricted Heisenberg Hamiltonian.

The next PR (α-5e) will prove irreducibility of `B` from the
swap-connectivity (PR α-5c).  PR α-5f will then apply PF and
conclude uniqueness of the H_0 ground state with `c_σ > 0`.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41 (proof of Theorem 2.2).
- E. Seneta, *Non-negative Matrices and Markov Chains*, 3rd ed.,
  Springer 2006, §1.1.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Definition of the shifted matrix -/

/-- The shifted dressed Heisenberg matrix `B := c · I − M` on
`H_0`, where `M = dressedHeisenbergMatrixH0 A J`. Used as input
for the Perron–Frobenius theorem. -/
noncomputable def dressedHeisenbergShifted (A : Λ → Bool)
    (J : Λ → Λ → ℂ) (c : ℝ) :
    Matrix (H₀Index Λ) (H₀Index Λ) ℝ :=
  fun σ τ =>
    (if σ = τ then c else 0) - dressedHeisenbergMatrixH0 A J σ τ

@[simp] theorem dressedHeisenbergShifted_apply
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (c : ℝ)
    (σ τ : H₀Index Λ) :
    dressedHeisenbergShifted A J c σ τ =
      (if σ = τ then c else 0) - dressedHeisenbergMatrixH0 A J σ τ := rfl

theorem dressedHeisenbergShifted_diag
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (c : ℝ)
    (σ : H₀Index Λ) :
    dressedHeisenbergShifted A J c σ σ =
      c - dressedHeisenbergMatrixH0 A J σ σ := by
  simp [dressedHeisenbergShifted]

theorem dressedHeisenbergShifted_off_diag
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (c : ℝ)
    {σ τ : H₀Index Λ} (hne : σ ≠ τ) :
    dressedHeisenbergShifted A J c σ τ =
      - dressedHeisenbergMatrixH0 A J σ τ := by
  simp [dressedHeisenbergShifted, hne]

/-! ## Symmetry -/

/-- The shifted matrix `B = c·I − M` is symmetric for real symmetric
`J`. Inherits symmetry from `M` (the identity term `(if σ = τ then c
else 0)` is trivially symmetric in `σ, τ`). -/
theorem dressedHeisenbergShifted_isSymm (A : Λ → Bool)
    {J : Λ → Λ → ℂ} (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_symm : ∀ x y, J x y = J y x) (c : ℝ) :
    (dressedHeisenbergShifted (Λ := Λ) A J c).IsSymm := by
  ext σ τ
  rw [Matrix.transpose_apply]
  simp only [dressedHeisenbergShifted_apply]
  congr 1
  · -- (if σ = τ ∨ τ = σ): symmetric `if`
    by_cases h : σ = τ
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  · -- M is symmetric (PR α-5a).
    have := dressedHeisenbergMatrixH0_isSymm A hJ_real hJ_symm
    have heq := congrFun (congrFun this τ) σ
    rw [Matrix.transpose_apply] at heq
    exact heq.symm

/-! ## Non-negativity for `c ≥ M σ σ` -/

/-- Off-diagonal entries of `B = c·I − M` are non-negative.
Direct from PR α-5a's `dressedHeisenbergMatrixH0_offdiag_nonpos`. -/
theorem dressedHeisenbergShifted_offdiag_nonneg
    (A : Λ → Bool)
    {J : Λ → Λ → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (c : ℝ) {σ τ : H₀Index Λ} (hne : σ ≠ τ) :
    0 ≤ dressedHeisenbergShifted A J c σ τ := by
  rw [dressedHeisenbergShifted_off_diag _ _ _ hne]
  linarith [dressedHeisenbergMatrixH0_offdiag_nonpos A hJ_real hJ_nn hJ_bipartite hne]

/-- Diagonal entries of `B = c·I − M` are non-negative if `c ≥ M σ σ`
for every `σ`. -/
theorem dressedHeisenbergShifted_diag_nonneg
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (c : ℝ)
    (hc : ∀ σ : H₀Index Λ, dressedHeisenbergMatrixH0 A J σ σ ≤ c)
    (σ : H₀Index Λ) :
    0 ≤ dressedHeisenbergShifted A J c σ σ := by
  rw [dressedHeisenbergShifted_diag]
  linarith [hc σ]

/-- All entries of `B = c·I − M` are non-negative under the
hypotheses on `J` and the diagonal-shift bound on `c`. -/
theorem dressedHeisenbergShifted_nonneg
    (A : Λ → Bool)
    {J : Λ → Λ → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (c : ℝ)
    (hc : ∀ σ : H₀Index Λ, dressedHeisenbergMatrixH0 A J σ σ ≤ c)
    (σ τ : H₀Index Λ) :
    0 ≤ dressedHeisenbergShifted A J c σ τ := by
  by_cases h : σ = τ
  · rw [h]; exact dressedHeisenbergShifted_diag_nonneg A J c hc τ
  · exact dressedHeisenbergShifted_offdiag_nonneg A hJ_real hJ_nn hJ_bipartite c h

end LatticeSystem.Quantum
