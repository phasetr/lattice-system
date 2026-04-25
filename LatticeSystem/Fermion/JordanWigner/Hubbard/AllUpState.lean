/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetry

/-!
# Hubbard all-up-spin state: no double occupancy + kinetic eigenvalue (Tasaki §11.1.1)

This file defines the fully spin-polarised (all-up-spin) state for the
spinful Hubbard model on `N + 1` sites, and proves that the on-site
interaction `H_int` annihilates it and that `H_hop` has a known
diagonal eigenvalue:

| Lean name | Statement |
|---|---|
| `hubbardAllUpState` | definition of `|↑…↑⟩` |
| `fermionUpNumber_mulVec_allUpState` | `n_{i,↑} · |↑…↑⟩ = |↑…↑⟩` |
| `fermionDownNumber_mulVec_allUpState` | `n_{i,↓} · |↑…↑⟩ = 0` |
| `fermionDownAnnihilation_mulVec_allUpState` | `c_{i,↓} · |↑…↑⟩ = 0` |
| `fermionUpCreation_mulVec_allUpState` | `c†_{i,↑} · |↑…↑⟩ = 0` |
| `hubbardOnSiteInteraction_mulVec_allUpState` | `H_int · |↑…↑⟩ = 0` |
| `hubbardKinetic_mulVec_allUpState` | `H_hop · |↑…↑⟩ = (Σ_i t i i) • |↑…↑⟩` |
| `hubbardHamiltonian_mulVec_allUpState_eigenstate` | `H · |↑…↑⟩ = (Σ_i t i i) • |↑…↑⟩` |

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

/-! ## Creation/annihilation operators on the all-up state -/

/-- Spin-down annihilation at site `i` annihilates the all-up state:
`c_{i,↓} · |↑…↑⟩ = 0`.

The spin-down JW index `2*i+1` is odd, so the all-up configuration
has occupation 0 there; the inner `σ^+` factor maps column 0 to 0. -/
theorem fermionDownAnnihilation_mulVec_allUpState (N : ℕ) (i : Fin (N + 1)) :
    (fermionDownAnnihilation N i).mulVec (hubbardAllUpState N) = 0 := by
  unfold fermionDownAnnihilation fermionMultiAnnihilation hubbardAllUpState
  rw [← Matrix.mulVec_mulVec]
  have hinner : (onSite (spinfulIndex N i 1) spinHalfOpPlus).mulVec
      (basisVec (fun k : Fin (2 * N + 2) =>
        if k.val % 2 = 0 then (1 : Fin 2) else 0)) = 0 := by
    rw [onSite_mulVec_basisVec]
    funext τ
    apply Finset.sum_eq_zero
    intro k _
    change spinHalfOpPlus k
        ((fun j : Fin (2 * N + 2) => if j.val % 2 = 0 then (1 : Fin 2) else 0)
          (spinfulIndex N i 1)) *
      basisVec (Function.update (fun j : Fin (2 * N + 2) =>
          if j.val % 2 = 0 then (1 : Fin 2) else 0)
        (spinfulIndex N i 1) k) τ = 0
    simp only [if_neg (show ¬(spinfulIndex N i 1).val % 2 = 0 from by
      have := spinfulIndex_down_odd N i; omega)]
    fin_cases k <;> simp [spinHalfOpPlus]
  rw [hinner, Matrix.mulVec_zero]

/-- Spin-up creation at site `i` annihilates the all-up state:
`c†_{i,↑} · |↑…↑⟩ = 0`.

The spin-up JW index `2*i` is even, so the all-up configuration has
occupation 1 there (site already occupied); the inner `σ^-` factor
maps column 1 to 0, giving 0. -/
theorem fermionUpCreation_mulVec_allUpState (N : ℕ) (i : Fin (N + 1)) :
    (fermionUpCreation N i).mulVec (hubbardAllUpState N) = 0 := by
  unfold fermionUpCreation fermionMultiCreation hubbardAllUpState
  rw [← Matrix.mulVec_mulVec]
  have hinner : (onSite (spinfulIndex N i 0) spinHalfOpMinus).mulVec
      (basisVec (fun k : Fin (2 * N + 2) =>
        if k.val % 2 = 0 then (1 : Fin 2) else 0)) = 0 := by
    rw [onSite_mulVec_basisVec]
    funext τ
    apply Finset.sum_eq_zero
    intro k _
    change spinHalfOpMinus k
        ((fun j : Fin (2 * N + 2) => if j.val % 2 = 0 then (1 : Fin 2) else 0)
          (spinfulIndex N i 0)) *
      basisVec (Function.update (fun j : Fin (2 * N + 2) =>
          if j.val % 2 = 0 then (1 : Fin 2) else 0)
        (spinfulIndex N i 0) k) τ = 0
    simp only [if_pos (spinfulIndex_up_even N i)]
    fin_cases k <;> simp [spinHalfOpMinus]
  rw [hinner, Matrix.mulVec_zero]

/-! ## Kinetic eigenvalue -/

set_option maxHeartbeats 400000 in
-- The double Finset.sum over (i, j) pairs causes elaboration to exceed the default limit.
/-- The Hubbard kinetic operator (hopping) on the all-up state gives
the diagonal trace of the hopping matrix:
`H_hop · |↑…↑⟩ = (Σ_i t i i) • |↑…↑⟩`.

Proof sketch:
- Down-spin hopping: `c_{j,↓} · |↑…↑⟩ = 0`, so each down-spin term vanishes.
- Up-spin off-diagonal (i ≠ j): using `{c_{j,↑}, c†_{i,↑}} = 0` we get
  `c†_{i,↑} c_{j,↑} = -c_{j,↑} c†_{i,↑}`, and `c†_{i,↑} · |↑…↑⟩ = 0`,
  so the off-diagonal terms vanish.
- Up-spin diagonal (i = j): `c†_{i,↑} c_{i,↑} · |↑…↑⟩ = n_{i,↑} · |↑…↑⟩ = |↑…↑⟩`.

Reference: Tasaki §11.1.1, p. 373. -/
private theorem hubbardKinetic_upSpin_mulVec_allUpState
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        t i j • (fermionUpCreation N i * fermionUpAnnihilation N j).mulVec
          (hubbardAllUpState N) =
      (∑ i : Fin (N + 1), t i i) • hubbardAllUpState N := by
  have off_zero : ∀ i j : Fin (N + 1), i ≠ j →
      (fermionUpCreation N i * fermionUpAnnihilation N j).mulVec
        (hubbardAllUpState N) = 0 := fun i j hij => by
    have h_ac : fermionUpCreation N i * fermionUpAnnihilation N j =
        -(fermionUpAnnihilation N j * fermionUpCreation N i) :=
      eq_neg_of_add_eq_zero_right
        (fermionUpAnnihilation_upCreation_anticomm_ne N hij.symm)
    rw [h_ac, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec,
      fermionUpCreation_mulVec_allUpState N i, Matrix.mulVec_zero, neg_zero]
  calc ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
        t i j • (fermionUpCreation N i * fermionUpAnnihilation N j).mulVec
          (hubbardAllUpState N)
      = ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
            if i = j then t i i • hubbardAllUpState N else 0 := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        by_cases hij : i = j
        · subst hij
          rw [show (fermionUpCreation N i * fermionUpAnnihilation N i).mulVec
              (hubbardAllUpState N) = hubbardAllUpState N from
            fermionUpNumber_mulVec_allUpState N i]
          simp
        · rw [off_zero i j hij, smul_zero, if_neg hij]
    _ = (∑ i : Fin (N + 1), t i i) • hubbardAllUpState N := by
        have h : ∀ i : Fin (N + 1), ∑ j : Fin (N + 1),
            (if i = j then t i i • hubbardAllUpState N else 0) =
              t i i • hubbardAllUpState N :=
          fun i => Fintype.sum_ite_eq i (fun _ => t i i • hubbardAllUpState N)
        simp_rw [h]
        exact Finset.sum_smul.symm

theorem hubbardKinetic_mulVec_allUpState
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    (hubbardKinetic N t).mulVec (hubbardAllUpState N) =
      (∑ i : Fin (N + 1), t i i) • hubbardAllUpState N := by
  unfold hubbardKinetic
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec]
  rw [Fin.sum_univ_two]
  -- Down-spin terms (σ = 1) each vanish
  have h_down : ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
      t i j • (fermionMultiCreation (2 * N + 1) (spinfulIndex N i 1) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j 1)).mulVec
          (hubbardAllUpState N) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      rw [← Matrix.mulVec_mulVec,
        show (fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j 1)).mulVec
            (hubbardAllUpState N) = 0 from fermionDownAnnihilation_mulVec_allUpState N j,
        Matrix.mulVec_zero, smul_zero]
  -- Up-spin (σ = 0): fermionMultiCreation/Annihilation at σ=0 equals
  -- fermionUpCreation/Annihilation by definition
  have h_up : ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
      t i j • (fermionMultiCreation (2 * N + 1) (spinfulIndex N i 0) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j 0)).mulVec
          (hubbardAllUpState N) = (∑ i : Fin (N + 1), t i i) • hubbardAllUpState N :=
    hubbardKinetic_upSpin_mulVec_allUpState N t
  rw [h_down, add_zero, h_up]

/-- The Hubbard Hamiltonian has `|↑…↑⟩` as an eigenstate with eigenvalue
`Σ_i t i i` (the trace of the hopping matrix):
`H · |↑…↑⟩ = (Σ_i t i i) • |↑…↑⟩`.

For the open chain (`hubbardChainHamiltonian`) with zero on-site potential
(no `t i i` term), this gives eigenvalue 0. -/
theorem hubbardHamiltonian_mulVec_allUpState_eigenstate
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    (hubbardHamiltonian N t U).mulVec (hubbardAllUpState N) =
      (∑ i : Fin (N + 1), t i i) • hubbardAllUpState N := by
  rw [hubbardHamiltonian_mulVec_allUpState, hubbardKinetic_mulVec_allUpState]

end LatticeSystem.Fermion
