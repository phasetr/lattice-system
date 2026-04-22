/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState.Definition

/-!
# 2D checkerboard Néel state definition (Tasaki §2.5)

Tasaki §2.5 eq. (2.5.2) defines the Néel state on a *bipartite*
lattice. The 2D square lattice with even sides is bipartite via
the parity sum colouring `(i, j) ↦ (i.val + j.val) % 2` (each
sublattice is a checkerboard). The corresponding Néel
configuration is `σ(i, j) := if (i.val + j.val) % 2 = 0 then ↑
else ↓`.

(Refactor Phase 2 PR 3 — third step of the NeelState 7-file
split, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The 2D checkerboard Néel configuration on
`Fin (2 * K) × Fin (2 * L)`: the spin at site `(i, j)` is `↑` if
`(i.val + j.val)` is even, `↓` otherwise. -/
def neelSquareConfig (K L : ℕ) :
    Fin (2 * K) × Fin (2 * L) → Fin 2 :=
  fun p => if (p.1.val + p.2.val) % 2 = 0 then 0 else 1

/-- The 2D Néel state on `Fin (2 * K) × Fin (2 * L)` for `S = 1/2`
(Tasaki §2.5 eq. (2.5.2) checkerboard instance). -/
noncomputable def neelSquareState (K L : ℕ) :
    (Fin (2 * K) × Fin (2 * L) → Fin 2) → ℂ :=
  basisVec (neelSquareConfig K L)

/-- 1D parity-sum lemma with a fixed parity offset: for any
`parity : ℕ` and `L : ℕ`,

  `Σ_{j : Fin (2*L)} (if (parity + j.val) % 2 = 0 then 1 else -1) = 0`.

Proof by induction on `L`, peeling the last two indices. -/
lemma sum_alternating_sign_offset (parity L : ℕ) :
    (∑ j : Fin (2 * L),
      (if (parity + j.val) % 2 = 0 then (1 : ℤ) else -1)) = 0 := by
  induction L with
  | zero => simp
  | succ L' ih =>
    rw [show 2 * (L' + 1) = (2 * L' + 1) + 1 from by ring]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h_inner_eq :
        (∑ j : Fin (2 * L'),
          if (parity + (j.castSucc.castSucc :
                Fin (2 * L' + 1 + 1)).val) % 2 = 0
            then (1 : ℤ) else -1) =
        ∑ j : Fin (2 * L'),
          (if (parity + j.val) % 2 = 0 then (1 : ℤ) else -1) := by
      apply Finset.sum_congr rfl
      intro j _
      rfl
    rw [h_inner_eq, ih]
    have h_last_outer :
        (Fin.last (2 * L' + 1)).val = 2 * L' + 1 := rfl
    have h_last_inner :
        ((Fin.last (2 * L')).castSucc :
          Fin (2 * L' + 1 + 1)).val = 2 * L' := rfl
    rw [h_last_outer, h_last_inner]
    rcases Nat.mod_two_eq_zero_or_one parity with hp0 | hp1
    · have h1 : (parity + 2 * L') % 2 = 0 := by omega
      have h2 : (parity + (2 * L' + 1)) % 2 ≠ 0 := by omega
      rw [if_pos h1, if_neg h2]; ring
    · have h1 : (parity + 2 * L') % 2 ≠ 0 := by omega
      have h2 : (parity + (2 * L' + 1)) % 2 = 0 := by omega
      rw [if_neg h1, if_pos h2]; ring

/-- The 2D Néel configuration on `Fin (2K) × Fin (2L)` has zero
total magnetisation: each row contributes a vanishing alternating
column sum (per `sum_alternating_sign_offset` at `parity = i.val`). -/
theorem neelSquareConfig_magnetization_zero (K L : ℕ) :
    magnetization (Fin (2 * K) × Fin (2 * L))
        (neelSquareConfig K L) = 0 := by
  unfold magnetization
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  unfold neelSquareConfig spinSign
  have h_inner : ∀ j : Fin (2 * L),
      (if ((if (i.val + j.val) % 2 = 0 then (0 : Fin 2) else 1) = 0)
        then (1 : ℤ) else -1) =
      (if (i.val + j.val) % 2 = 0 then (1 : ℤ) else -1) := by
    intro j
    by_cases hp : (i.val + j.val) % 2 = 0
    · simp [hp]
    · simp [hp]
  simp_rw [h_inner]
  exact sum_alternating_sign_offset i.val L

/-- The 2D Néel state on `Fin (2*K) × Fin (2*L)` lies in the
zero-magnetisation sector `H_0`. -/
theorem neelSquareState_mem_magnetizationSubspace_zero (K L : ℕ) :
    neelSquareState K L ∈
      magnetizationSubspace (Fin (2 * K) × Fin (2 * L)) (0 : ℂ) := by
  unfold neelSquareState
  have h := basisVec_mem_magnetizationSubspace
    (Λ := Fin (2 * K) × Fin (2 * L)) (neelSquareConfig K L)
  rw [neelSquareConfig_magnetization_zero] at h
  simpa using h

end LatticeSystem.Quantum
