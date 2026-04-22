/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState.Definition2D

/-!
# 3D cubic checkerboard Néel state definition (Tasaki §2.5)

3D analogue of the checkerboard Néel state: at site `((i, j), k)`,
the spin is `↑` if `(i + j + k) % 2 = 0`, `↓` otherwise. The
3D magnetisation is computed by reducing one dimension at a time
to `sum_alternating_sign_offset` (introduced in `Definition2D.lean`).

(Refactor Phase 2 PR 4 — fourth step of the NeelState 7-file
split, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The 3D cubic checkerboard Néel configuration on
`(Fin (2K) × Fin (2L)) × Fin (2M)`. -/
def neelCubicConfig (K L M : ℕ) :
    (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2 :=
  fun p =>
    if (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0 then 0 else 1

/-- The 3D cubic Néel state. -/
noncomputable def neelCubicState (K L M : ℕ) :
    ((Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2) → ℂ :=
  basisVec (neelCubicConfig K L M)

/-- Magnetisation of the 3D cubic Néel configuration vanishes:
the outer-most sum (over `k : Fin (2*M)`) for each fixed
`((i, j))` is an alternating offset sum. -/
theorem neelCubicConfig_magnetization_zero (K L M : ℕ) :
    magnetization
        ((Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
        (neelCubicConfig K L M) = 0 := by
  unfold magnetization
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro p _
  unfold neelCubicConfig spinSign
  have h_inner : ∀ k : Fin (2 * M),
      (if ((if (p.1.val + p.2.val + k.val) % 2 = 0
              then (0 : Fin 2) else 1) = 0)
        then (1 : ℤ) else -1) =
      (if (p.1.val + p.2.val + k.val) % 2 = 0
        then (1 : ℤ) else -1) := by
    intro k
    by_cases hp : (p.1.val + p.2.val + k.val) % 2 = 0
    · simp [hp]
    · simp [hp]
  simp_rw [h_inner]
  exact sum_alternating_sign_offset (p.1.val + p.2.val) M

/-- The 3D cubic Néel state lies in the zero-magnetisation
sector `H_0`. -/
theorem neelCubicState_mem_magnetizationSubspace_zero
    (K L M : ℕ) :
    neelCubicState K L M ∈
      magnetizationSubspace
        ((Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
        (0 : ℂ) := by
  unfold neelCubicState
  have h := basisVec_mem_magnetizationSubspace
    (Λ := (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
    (neelCubicConfig K L M)
  rw [neelCubicConfig_magnetization_zero] at h
  simpa using h

end LatticeSystem.Quantum
