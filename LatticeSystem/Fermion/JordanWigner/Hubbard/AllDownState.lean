import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry

/-!
# Hubbard all-down-spin state: no double occupancy (mirror of `AllUpState`)

This file defines the fully spin-polarised (all-down-spin) state
for the spinful Hubbard model on `N + 1` sites. The all-down
state has occupation `1` on odd JW indices (spin-down sites)
and `0` on even JW indices (spin-up sites). It is the up/down
symmetric mirror of `hubbardAllUpState`.

| Lean name | Statement |
|---|---|
| `hubbardAllDownState` | definition of `|↓…↓⟩` |
| `fermionDownNumber_mulVec_allDownState` | `n_{i,↓} · |↓…↓⟩ = |↓…↓⟩` |
| `fermionUpNumber_mulVec_allDownState` | `n_{i,↑} · |↓…↓⟩ = 0` |
| `fermionUpAnnihilation_mulVec_allDownState` | `c_{i,↑} · |↓…↓⟩ = 0` |
| `fermionDownCreation_mulVec_allDownState` | `c†_{i,↓} · |↓…↓⟩ = 0` |
| `hubbardOnSiteInteraction_mulVec_allDownState` | `H_int · |↓…↓⟩ = 0` |

By up/down symmetry these are identical to the all-up
counterparts. The on-site Hubbard interaction annihilates both
fully polarised states, so they belong to its kernel.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-! ## Definition -/

/-- The all-down-spin state for the spinful Hubbard model on
`N + 1` sites: all spin-down orbitals occupied, all spin-up
orbitals empty.

In the Jordan–Wigner representation on `Fin (2 * N + 2)`,
even indices carry spin-up (empty) and odd indices carry
spin-down (occupied). -/
noncomputable def hubbardAllDownState (N : ℕ) :
    (Fin (2 * N + 2) → Fin 2) → ℂ :=
  basisVec (fun k : Fin (2 * N + 2) => if k.val % 2 = 0 then 0 else 1)

/-! ## Auxiliary: parity of spinful JW indices -/

/-- The spin-up JW index `spinfulIndex N i 0` has even value. -/
private theorem spinfulIndex_up_even' (N : ℕ) (i : Fin (N + 1)) :
    (spinfulIndex N i 0).val % 2 = 0 := by
  simp [spinfulIndex]

/-- The spin-down JW index `spinfulIndex N i 1` has odd value. -/
private theorem spinfulIndex_down_odd' (N : ℕ) (i : Fin (N + 1)) :
    (spinfulIndex N i 1).val % 2 = 1 := by
  simp [spinfulIndex]

/-! ## Number-operator action on the all-down state -/

/-- The spin-down number operator at site `i` acts as the
identity on `hubbardAllDownState`: `n_{i,↓} · |↓…↓⟩ = |↓…↓⟩`. -/
theorem fermionDownNumber_mulVec_allDownState (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownNumber N i).mulVec (hubbardAllDownState N) =
      hubbardAllDownState N := by
  unfold fermionDownNumber hubbardAllDownState
  rw [fermionMultiNumber_eq_onSite, onSite_mulVec_basisVec]
  funext τ
  -- spin-down site is odd, so the all-down configuration has occupation 1.
  have hodd : ¬(spinfulIndex N i 1).val % 2 = 0 := by
    have := spinfulIndex_down_odd' N i; omega
  simp only [if_neg hodd]
  rw [Fin.sum_univ_two]
  have h0 : (spinHalfOpMinus * spinHalfOpPlus) (0 : Fin 2) (1 : Fin 2) = 0 := by
    simp [spinHalfOpMinus, spinHalfOpPlus]
  have h1 : (spinHalfOpMinus * spinHalfOpPlus) (1 : Fin 2) (1 : Fin 2) = 1 := by
    simp [spinHalfOpMinus, spinHalfOpPlus]
  rw [h0, zero_mul, zero_add, h1, one_mul]
  congr 1
  funext k
  by_cases hk : k = spinfulIndex N i 1
  · subst hk
    simp [hodd]
  · simp [Function.update_of_ne hk]

/-- The spin-up number operator at site `i` annihilates the
all-down state: `n_{i,↑} · |↓…↓⟩ = 0`. -/
theorem fermionUpNumber_mulVec_allDownState (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpNumber N i).mulVec (hubbardAllDownState N) = 0 := by
  unfold fermionUpNumber hubbardAllDownState
  rw [fermionMultiNumber_eq_onSite, onSite_mulVec_basisVec]
  funext τ
  apply Finset.sum_eq_zero
  intro k _
  change (spinHalfOpMinus * spinHalfOpPlus) k
      ((fun j : Fin (2 * N + 2) => if j.val % 2 = 0 then (0 : Fin 2) else 1)
        (spinfulIndex N i 0)) *
    basisVec (Function.update (fun j : Fin (2 * N + 2) =>
        if j.val % 2 = 0 then (0 : Fin 2) else 1)
      (spinfulIndex N i 0) k) τ = 0
  simp only [if_pos (spinfulIndex_up_even' N i)]
  fin_cases k <;> simp [spinHalfOpMinus, spinHalfOpPlus]

/-! ## Interaction on all-down state -/

/-- The on-site Hubbard interaction `H_int = U Σ n_{i,↑} n_{i,↓}`
annihilates the all-down state. -/
theorem hubbardOnSiteInteraction_mulVec_allDownState (N : ℕ) (U : ℂ) :
    (hubbardOnSiteInteraction N U).mulVec (hubbardAllDownState N) = 0 := by
  unfold hubbardOnSiteInteraction
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro i _
  -- Each summand U • (n_↑ * n_↓) · |↓..⟩ = 0
  --   = U • (n_↑ · (n_↓ · |↓..⟩)) = U • (n_↑ · |↓..⟩) = 0
  --   by fermionUpNumber_mulVec_allDownState (since n_↓ |↓..⟩ = |↓..⟩).
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    fermionDownNumber_mulVec_allDownState,
    fermionUpNumber_mulVec_allDownState, smul_zero]

/-! ## Creation/annihilation operators on the all-down state -/

/-- Spin-up annihilation at site `i` annihilates the all-down state:
`c_{i,↑} · |↓…↓⟩ = 0`. -/
theorem fermionUpAnnihilation_mulVec_allDownState (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpAnnihilation N i).mulVec (hubbardAllDownState N) = 0 := by
  unfold fermionUpAnnihilation fermionMultiAnnihilation hubbardAllDownState
  rw [← Matrix.mulVec_mulVec]
  have hinner : (onSite (spinfulIndex N i 0) spinHalfOpPlus).mulVec
      (basisVec (fun k : Fin (2 * N + 2) =>
        if k.val % 2 = 0 then (0 : Fin 2) else 1)) = 0 := by
    rw [onSite_mulVec_basisVec]
    funext τ
    apply Finset.sum_eq_zero
    intro k _
    change spinHalfOpPlus k
        ((fun j : Fin (2 * N + 2) => if j.val % 2 = 0 then (0 : Fin 2) else 1)
          (spinfulIndex N i 0)) *
      basisVec (Function.update (fun j : Fin (2 * N + 2) =>
          if j.val % 2 = 0 then (0 : Fin 2) else 1)
        (spinfulIndex N i 0) k) τ = 0
    simp only [if_pos (spinfulIndex_up_even' N i)]
    fin_cases k <;> simp [spinHalfOpPlus]
  rw [hinner, Matrix.mulVec_zero]

/-- Spin-down creation at site `i` annihilates the all-down state:
`c†_{i,↓} · |↓…↓⟩ = 0`. -/
theorem fermionDownCreation_mulVec_allDownState (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownCreation N i).mulVec (hubbardAllDownState N) = 0 := by
  unfold fermionDownCreation fermionMultiCreation hubbardAllDownState
  rw [← Matrix.mulVec_mulVec]
  have hinner : (onSite (spinfulIndex N i 1) spinHalfOpMinus).mulVec
      (basisVec (fun k : Fin (2 * N + 2) =>
        if k.val % 2 = 0 then (0 : Fin 2) else 1)) = 0 := by
    rw [onSite_mulVec_basisVec]
    funext τ
    apply Finset.sum_eq_zero
    intro k _
    change spinHalfOpMinus k
        ((fun j : Fin (2 * N + 2) => if j.val % 2 = 0 then (0 : Fin 2) else 1)
          (spinfulIndex N i 1)) *
      basisVec (Function.update (fun j : Fin (2 * N + 2) =>
          if j.val % 2 = 0 then (0 : Fin 2) else 1)
        (spinfulIndex N i 1) k) τ = 0
    have hodd : ¬(spinfulIndex N i 1).val % 2 = 0 := by
      have := spinfulIndex_down_odd' N i; omega
    simp only [if_neg hodd]
    fin_cases k <;> simp [spinHalfOpMinus]
  rw [hinner, Matrix.mulVec_zero]

end LatticeSystem.Fermion
