/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.Hubbard.Charges

/-!
# Hubbard all-up-spin state: no double occupancy (Tasaki §11.1.1)

This file defines the fully spin-polarised (all-up-spin) state for the
spinful Hubbard model on `N + 1` sites, and proves that the on-site
interaction `H_int` annihilates it:

| Lean name | Statement |
|---|---|
| `hubbardAllUpState` | definition of `|↑…↑⟩` |
| `fermionUpNumber_mulVec_allUpState` | `n_{i,↑} · |↑…↑⟩ = |↑…↑⟩` |
| `fermionDownNumber_mulVec_allUpState` | `n_{i,↓} · |↑…↑⟩ = 0` |
| `hubbardOnSiteInteraction_mulVec_allUpState` | `H_int · |↑…↑⟩ = 0` |
| `hubbardHamiltonian_mulVec_allUpState` | `H · |↑…↑⟩ = H_hop · |↑…↑⟩` |

These results are the algebraic content of Tasaki §11.1.1, p. 373
(the polarised sector reduces to a non-interacting model), and they
underlie eq. (10.1.5) on p. 344.

## JW-index convention

In the spinful JW chain on `Fin (2 * N + 2)`:
* spin-up  site `i` ↦ JW index `2 * i`   (even)
* spin-down site `i` ↦ JW index `2 * i + 1` (odd)

The all-up state is therefore the basis vector whose occupation is
`1` on even JW indices and `0` on odd JW indices.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-! ## Definition -/

/-- The all-up-spin state for the spinful Hubbard model on `N + 1`
sites: all spin-up orbitals occupied, all spin-down orbitals empty.

In the Jordan–Wigner representation on `Fin (2 * N + 2)`, even
indices carry spin-up (occupied) and odd indices carry spin-down
(empty). -/
noncomputable def hubbardAllUpState (N : ℕ) :
    (Fin (2 * N + 2) → Fin 2) → ℂ :=
  basisVec (fun k : Fin (2 * N + 2) => if k.val % 2 = 0 then 1 else 0)

/-! ## Auxiliary: parity of spinful JW indices -/

/-- The spin-up JW index `spinfulIndex N i 0` has even value. -/
private theorem spinfulIndex_up_even (N : ℕ) (i : Fin (N + 1)) :
    (spinfulIndex N i 0).val % 2 = 0 := by
  simp [spinfulIndex]

/-- The spin-down JW index `spinfulIndex N i 1` has odd value. -/
private theorem spinfulIndex_down_odd (N : ℕ) (i : Fin (N + 1)) :
    (spinfulIndex N i 1).val % 2 = 1 := by
  simp [spinfulIndex]

/-! ## Number-operator action on the all-up state -/

/-- The spin-up number operator at site `i` acts as the identity on
`hubbardAllUpState`: `n_{i,↑} · |↑…↑⟩ = |↑…↑⟩`.

The spin-up JW index `2*i` is even, so the all-up configuration has
occupation 1 there; `(σ^- σ^+) k 1 = δ_{k,1}` and the surviving
term reproduces `|↑…↑⟩`. -/
theorem fermionUpNumber_mulVec_allUpState (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i).mulVec (hubbardAllUpState N) = hubbardAllUpState N := by
  unfold fermionUpNumber hubbardAllUpState
  rw [fermionMultiNumber_eq_onSite, onSite_mulVec_basisVec]
  funext τ
  simp only [if_pos (spinfulIndex_up_even N i)]
  rw [Fin.sum_univ_two]
  have h0 : (spinHalfOpMinus * spinHalfOpPlus) (0 : Fin 2) (1 : Fin 2) = 0 := by
    simp [spinHalfOpMinus, spinHalfOpPlus]
  have h1 : (spinHalfOpMinus * spinHalfOpPlus) (1 : Fin 2) (1 : Fin 2) = 1 := by
    simp [spinHalfOpMinus, spinHalfOpPlus]
  rw [h0, zero_mul, zero_add, h1, one_mul]
  congr 1
  funext k
  by_cases hk : k = spinfulIndex N i 0
  · subst hk
    simp [spinfulIndex_up_even N i]
  · simp [Function.update_of_ne hk]

/-- The spin-down number operator at site `i` annihilates the
all-up state: `n_{i,↓} · |↑…↑⟩ = 0`.

The spin-down JW index `2*i+1` is odd, so the all-up configuration
has occupation 0 there; `(σ^- σ^+) k 0 = 0` for both `k`. -/
theorem fermionDownNumber_mulVec_allUpState (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownNumber N i).mulVec (hubbardAllUpState N) = 0 := by
  unfold fermionDownNumber hubbardAllUpState
  rw [fermionMultiNumber_eq_onSite, onSite_mulVec_basisVec]
  funext τ
  apply Finset.sum_eq_zero
  intro k _
  change (spinHalfOpMinus * spinHalfOpPlus) k
      ((fun j : Fin (2 * N + 2) => if j.val % 2 = 0 then (1 : Fin 2) else 0)
        (spinfulIndex N i 1)) *
    basisVec (Function.update (fun j : Fin (2 * N + 2) =>
        if j.val % 2 = 0 then (1 : Fin 2) else 0)
      (spinfulIndex N i 1) k) τ = 0
  simp only [if_neg (show ¬(spinfulIndex N i 1).val % 2 = 0 from by
    have := spinfulIndex_down_odd N i; omega)]
  fin_cases k <;> simp [spinHalfOpMinus, spinHalfOpPlus]

/-! ## Interaction and Hamiltonian on all-up state -/

/-- The on-site Hubbard interaction `H_int = U Σ n_{i,↑} n_{i,↓}`
annihilates the all-up state.

Each summand `n_{i,↑} n_{i,↓} · |↑…↑⟩ = n_{i,↑} · (n_{i,↓} · |↑…↑⟩) = 0`
by `fermionDownNumber_mulVec_allUpState`. -/
theorem hubbardOnSiteInteraction_mulVec_allUpState (N : ℕ) (U : ℂ) :
    (hubbardOnSiteInteraction N U).mulVec (hubbardAllUpState N) = 0 := by
  unfold hubbardOnSiteInteraction
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro i _
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    fermionDownNumber_mulVec_allUpState, Matrix.mulVec_zero, smul_zero]

/-- On the all-up state, the full Hubbard Hamiltonian reduces to the
kinetic (hopping) term: `H · |↑…↑⟩ = H_hop · |↑…↑⟩`.

Immediate from `H = H_hop + H_int` and
`hubbardOnSiteInteraction_mulVec_allUpState`. -/
theorem hubbardHamiltonian_mulVec_allUpState
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    (hubbardHamiltonian N t U).mulVec (hubbardAllUpState N) =
      (hubbardKinetic N t).mulVec (hubbardAllUpState N) := by
  unfold hubbardHamiltonian
  rw [Matrix.add_mulVec, hubbardOnSiteInteraction_mulVec_allUpState, add_zero]

end LatticeSystem.Fermion
