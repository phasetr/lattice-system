/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.DressedSwapValue
import LatticeSystem.Quantum.MarshallLiebMattis.H0Shifted

/-!
# Strict positivity of `B = c·I − M` on swap-related H_0 configurations

This module establishes the **strict positivity** of the shifted
dressed Heisenberg matrix on swap-related configurations:

  `0 < dressedHeisenbergShifted A J c σ τ`

when `τ.val = basisSwap σ.val x y` for a positive bipartite bond
`(x, y)` with `(J x y).re > 0`.

Combining:

* PR α-5i's exact dressed matrix value
  `dressedHeisenbergMatrixH0 A J σ τ = -(J x y).re < 0`,
* the off-diagonal definition `B σ τ = -M σ τ` (PR α-5d),

gives `B σ τ = (J x y).re > 0`. The hypothesis `σ ≠ τ` (needed
for the off-diagonal case of `B`) follows from `basisSwap_ne_self`
combined with `σ_x ≠ σ_y`.

This is the **single-step strict positivity** input needed for
Perron–Frobenius irreducibility of `B` (subsequent PRs).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Strict positivity of `B = c · I − M` on swap-related H_0
configurations. For bipartite `(Λ, A)` with positive symmetric real
coupling `J` on the bond `(x, y)` (with `A x ≠ A y`, antiparallel
`σ_x ≠ σ_y`), and any `c`,

  `0 < dressedHeisenbergShifted A J c σ τ`

when `τ.val = basisSwap σ.val x y`.

Proof: `σ ≠ τ` (from `basisSwap_ne_self`); off-diagonal entry
`B σ τ = -M σ τ`; `M σ τ = -(J x y).re` by α-5i, so
`B σ τ = (J x y).re > 0`. -/
theorem dressedHeisenbergShifted_pos_of_basisSwap
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJ_symm : ∀ x y, J x y = J y x)
    {x y : Λ} (hxy : x ≠ y) (hA : A x ≠ A y)
    (hJxy_pos : 0 < (J x y).re)
    (c : ℝ)
    {σ : H₀Index Λ} (h : σ.val x ≠ σ.val y)
    (τ : H₀Index Λ) (hτ : τ.val = basisSwap σ.val x y) :
    0 < dressedHeisenbergShifted A J c σ τ := by
  -- σ ≠ τ since σ.val ≠ τ.val (basisSwap σ.val x y ≠ σ.val).
  have hne : σ ≠ τ := by
    intro heq
    have hval : σ.val = τ.val := congrArg Subtype.val heq
    rw [hτ] at hval
    exact basisSwap_ne_self hxy h hval.symm
  -- Off-diagonal: B σ τ = -M σ τ.
  rw [dressedHeisenbergShifted_off_diag _ _ _ hne]
  -- M σ τ = -(J x y).re by α-5i.
  rw [dressedHeisenbergMatrixH0_apply_basisSwap A hJ_symm hxy hA h τ hτ]
  -- -(-(J x y).re) = (J x y).re > 0.
  linarith

end LatticeSystem.Quantum
