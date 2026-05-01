/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.H0ShiftedIrreducible
import LatticeSystem.Math.PerronFrobenius

/-!
# Perron–Frobenius application: H_0 ground-state expansion

This module applies the Perron–Frobenius theorem to the irreducible
non-negative shifted dressed Heisenberg matrix `B = c · I − M` on
`H_0` (assembled across PRs α-5a through α-5n) to obtain:

  there is a unique (up to positive scalar) strictly positive
  vector `v : H₀Index Λ → ℝ` and a real eigenvalue `μ` such that
  `B *ᵥ v = μ • v`.

Translating back to `M = c · I − B`: `v` is also an eigenvector of
`M` with eigenvalue `c − μ`; this is the **minimum** eigenvalue of
`M` since the maximum eigenvalue of `B` corresponds to the minimum
of `M`.

In Tasaki's notation (eq. (2.5.4)): the antiferromagnetic Heisenberg
ground state in `H_0` admits the unique expansion

  `|Φ_GS⟩ = Σ_σ c_σ |Ψ̃^σ⟩`  with  `c_σ > 0`,

where `c_σ = v σ` is the strictly positive Perron eigenvector.

The translation from "matrix eigenvector v" to "operator-level
ground-state |Φ_GS⟩" is left for subsequent work. This module
delivers the matrix-level uniqueness statement.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 39 eq. (2.5.4).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- The shifted dressed Heisenberg matrix is **Hermitian** (= symmetric
for real matrices) under real symmetric `J`. Wraps the IsSymm
result from PR α-5d into the IsHermitian form needed for PF. -/
theorem dressedHeisenbergShifted_isHermitian (A : Λ → Bool)
    {J : Λ → Λ → ℂ} (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_symm : ∀ x y, J x y = J y x) (c : ℝ) :
    Matrix.IsHermitian (dressedHeisenbergShifted A J c) := by
  apply Matrix.IsHermitian.ext
  intro i j
  -- For ℝ-valued matrices, star = id.
  change (dressedHeisenbergShifted A J c j i) =
      (dressedHeisenbergShifted A J c i j)
  exact (dressedHeisenbergShifted_isSymm A hJ_real hJ_symm c).apply i j

/-- **Perron–Frobenius applied to `B = c · I − M` on `H_0`.**

For a connected bipartite graph with positive symmetric real
coupling and `c > M σ σ` (strict), there exists a strictly positive
eigenvector `v` for some real eigenvalue `μ` of the shifted dressed
Heisenberg matrix `B`.  Equivalently, `v` is the "ground-state
eigenvector" of `M` (with eigenvalue `c − μ`, the minimum of `M`'s
spectrum). -/
theorem dressedHeisenbergShifted_exists_pos_eigenvec_max
    [Nonempty (H₀Index Λ)]
    {G : SimpleGraph Λ} (hG : G.Preconnected) (A : Λ → Bool)
    (hG_bipartite : ∀ {x y : Λ}, G.Adj x y → A x ≠ A y)
    {J : Λ → Λ → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_symm : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_on_G : ∀ {x y : Λ}, G.Adj x y → 0 < (J x y).re)
    (c : ℝ)
    (hc : ∀ σ : H₀Index Λ, dressedHeisenbergMatrixH0 A J σ σ < c) :
    ∃ (μ : ℝ) (v : H₀Index Λ → ℝ),
      (dressedHeisenbergShifted A J c).mulVec v = μ • v ∧
      v ≠ 0 ∧ ∀ σ, 0 < v σ := by
  exact LatticeSystem.Math.PerronFrobenius.exists_pos_eigenvec_max
    (dressedHeisenbergShifted_isHermitian A hJ_real hJ_symm c)
    (dressedHeisenbergShifted_isIrreducible hG A hG_bipartite hJ_real hJ_symm
      hJ_nn hJ_bipartite hJ_pos_on_G c hc)

/-- **Uniqueness of the strictly positive eigenvector** of
`B = c · I − M`. Combined with `dressedHeisenbergShifted_exists_pos_eigenvec_max`,
this yields Tasaki (2.5.4): the antiferromagnetic Heisenberg ground
state in `H_0` admits a unique expansion `Σ_σ c_σ |Ψ̃^σ⟩` with
`c_σ > 0` (here `c_σ = v σ` for the unique-up-to-positive-scalar
strictly positive eigenvector `v`). -/
theorem dressedHeisenbergShifted_pos_eigenvec_unique
    [Nonempty (H₀Index Λ)]
    {G : SimpleGraph Λ} (hG : G.Preconnected) (A : Λ → Bool)
    (hG_bipartite : ∀ {x y : Λ}, G.Adj x y → A x ≠ A y)
    {J : Λ → Λ → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_symm : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_on_G : ∀ {x y : Λ}, G.Adj x y → 0 < (J x y).re)
    (c : ℝ)
    (hc : ∀ σ : H₀Index Λ, dressedHeisenbergMatrixH0 A J σ σ < c)
    {μ : ℝ} {v w : H₀Index Λ → ℝ}
    (hv : (dressedHeisenbergShifted A J c).mulVec v = μ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (dressedHeisenbergShifted A J c).mulVec w = μ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    ∃ r : ℝ, 0 < r ∧ w = r • v :=
  LatticeSystem.Math.PerronFrobenius.pos_eigenvec_unique
    (dressedHeisenbergShifted_isIrreducible hG A hG_bipartite hJ_real hJ_symm
      hJ_nn hJ_bipartite hJ_pos_on_G c hc)
    hv hv_pos hw hw_pos

end LatticeSystem.Quantum
