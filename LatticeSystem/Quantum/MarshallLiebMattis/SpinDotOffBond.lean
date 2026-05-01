/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.HeisenbergSwapEntry

/-!
# Off-bond vanishing of `spinHalfDot` matrix entry on swap configurations

This module shows that for `σ' = basisSwap σ x y` with `x ≠ y`,
`σ_x ≠ σ_y`, and any bond `(u, v)` with `(u, v) ∉ {(x, y), (y, x)}`,
the matrix entry vanishes:

  `(spinHalfDot u v) σ σ' = 0`.

Three cases of `(u, v)`:

* `u = v`: the matrix is `(3/4) · I` (`spinHalfDot_self`); off-diagonal
  at `σ ≠ σ'` is `0`.
* `u ≠ v`, `σ'_u = σ'_v` (parallel `σ'` at `(u, v)`): the action gives
  `(1/4) · basisVec σ'`; off-diagonal at `σ ≠ σ'` is `0`.
* `u ≠ v`, `σ'_u ≠ σ'_v` (antiparallel `σ'`), `{u, v} ≠ {x, y}`: the
  action gives `(1/2) basisVec (basisSwap σ' u v) - (1/4) basisVec σ'`.
  Evaluation at `σ`: the second term is `0` (`σ ≠ σ'`); the first term
  vanishes because
  `basisSwap σ' u v ≠ σ` (PR α-5f's
  `basisSwap_basisSwap_ne_self_of_ne_bond`).

This combined with PR α-5e's `spinHalfDot_apply_basisSwap = 1/2`
(for the active bond pair) gives full information on the
`spinHalfDot u v` matrix entries needed to compute the Heisenberg
matrix entry sum in subsequent PRs.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Auxiliary: matrix entry via column expansion -/

/-- For any operator `M`, `M σ τ = (M.mulVec (basisVec τ)) σ`. -/
private theorem mulVec_basisVec_apply'' (M : ManyBodyOp Λ)
    (σ τ : Λ → Fin 2) :
    M σ τ = M.mulVec (basisVec τ) σ := by
  change M σ τ = dotProduct (fun j => M σ j) (basisVec τ)
  unfold dotProduct
  rw [sum_mul_basisVec τ (M σ)]

/-! ## Off-bond vanishing -/

/-- For `σ' = basisSwap σ x y` (with `x ≠ y`, `σ_x ≠ σ_y`) and any
bond `(u, v)` with `(u, v) ∉ {(x, y), (y, x)}`,
`(spinHalfDot u v) σ σ' = 0`.

Three sub-cases handled:
* `u = v`: identity-multiple, off-diagonal vanishes for `σ ≠ σ'`.
* `u ≠ v`, parallel σ' at `(u, v)`: action is a multiple of
  `basisVec σ'`, off-diagonal at `σ ≠ σ'` is zero.
* `u ≠ v`, antiparallel σ', off-bond: action gives a span involving
  `basisSwap σ' u v` and `σ'`, both of which differ from `σ` (the
  first by PR α-5f's combinatorial helper). -/
theorem spinHalfDot_apply_basisSwap_off_bond_eq_zero
    {x y u v : Λ} (hxy : x ≠ y)
    {σ : Λ → Fin 2} (h : σ x ≠ σ y)
    (hbond : ¬ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) :
    (spinHalfDot u v) σ (basisSwap σ x y) = 0 := by
  rw [mulVec_basisVec_apply'' (spinHalfDot u v) σ (basisSwap σ x y)]
  by_cases huv : u = v
  · -- u = v: spinHalfDot u u = (3/4) • 1, action is (3/4) • basisVec σ'.
    --   Off-diagonal at σ ≠ σ' = basisSwap σ x y is 0.
    subst huv
    rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.smul_apply, smul_eq_mul,
        basisVec_of_ne (basisSwap_ne_self hxy h).symm, mul_zero]
  · -- u ≠ v.  Cases on parallel/antiparallel of σ' at (u, v).
    by_cases hpar : (basisSwap σ x y) u = (basisSwap σ x y) v
    · -- Parallel σ' at (u, v): action is (1/4) • basisVec σ'.
      rw [spinHalfDot_mulVec_basisVec_parallel huv (basisSwap σ x y) hpar,
          Pi.smul_apply, smul_eq_mul,
          basisVec_of_ne (basisSwap_ne_self hxy h).symm, mul_zero]
    · -- Antiparallel σ' at (u, v): action is
      --   (1/2) basisVec (basisSwap σ' u v) - (1/4) basisVec σ'.
      rw [spinHalfDot_mulVec_basisVec_antiparallel huv (basisSwap σ x y) hpar]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [basisVec_of_ne (basisSwap_ne_self hxy h).symm, mul_zero, sub_zero]
      have hne : basisSwap (basisSwap σ x y) u v ≠ σ :=
        basisSwap_basisSwap_ne_self_of_ne_bond hxy h hbond
      rw [basisVec_of_ne (Ne.symm hne), mul_zero]

end LatticeSystem.Quantum
