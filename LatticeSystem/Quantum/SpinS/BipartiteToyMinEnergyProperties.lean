import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Properties of the predicted toy-Hamiltonian minimum energy

Edge cases and structural inequalities for the predicted toy-
Hamiltonian minimum energy defined in PR #2778:

  `bipartiteToyMinEnergyPredicted A N
     = (s_A − s_B)(s_A − s_B + 1) − s_A(s_A + 1) − s_B(s_B + 1)
     = −|A|·|¬A|·N²/2 − |¬A|·N`,

with `s_A = |A|·N/2, s_B = |¬A|·N/2`.

This file packages:

1. **Saturated edge case** (`|¬A| = 0`):
   `bipartiteToyMinEnergyPredicted = 0`, matching the trivial
   ground-state energy of the all-up state when no cross-bonds
   exist.
2. **Balanced edge case** (`|A| = |¬A|`): the predicted minimum
   reduces to `−2 s_A(s_A + 1) = -|V|·N·(|V|·N/2 + 1)/2` where
   `s_A = |A|·N/2 = (|V|·N/2)/2`. (This is the
   "anti-ferromagnetic-saturation" energy.)
3. **Néel-state gap**: the predicted minimum is strictly lower
   than the Néel-state toy-Hamiltonian expectation
   `−|A|·|¬A|·N²/2` by `|¬A|·N`, i.e. the Néel state is NOT the
   ground state unless `|¬A|·N = 0` (saturated case).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] {N : ℕ}

/-- **Saturated edge case**: when `|¬A| = 0` (no second
sublattice), the predicted toy-Hamiltonian minimum energy is zero,
matching the trivial spectrum of the empty cross-bond Hamiltonian. -/
theorem bipartiteToyMinEnergyPredicted_eq_zero_of_cardNotA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    bipartiteToyMinEnergyPredicted (Λ := Λ) A N = 0 := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified]
  rw [h]
  push_cast
  ring

/-- **Néel-state gap**: `bipartiteToyMinEnergyPredicted A N =
⟨Φ_Néel|Ĥ_toy_S|Φ_Néel⟩ − |¬A|·N`. The Néel expectation
exceeds the predicted minimum by `|¬A|·N ≥ 0`, with equality iff
`|¬A| = 0` or `N = 0` (degenerate cases). This shows the Néel
state is NOT the toy-Hamiltonian ground state in the
non-degenerate `|¬A|·N ≥ 1` regime. -/
theorem bipartiteToyMinEnergyPredicted_eq_neelExpectation_sub_cardNotA_mul_N
    (A : Λ → Bool) (N : ℕ) :
    bipartiteToyMinEnergyPredicted (Λ := Λ) A N =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) -
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          (N : ℂ)) := by
  exact bipartiteToyMinEnergyPredicted_eq_simplified A N

/-- **Balanced edge case**: when `|A| = |¬A|`, the imbalance term
`(s_A − s_B)(s_A − s_B + 1)` vanishes and the predicted minimum
collapses to `−2 s_A(s_A + 1)`. -/
theorem bipartiteToyMinEnergyPredicted_eq_balanced_form_of_card_eq
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card =
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    bipartiteToyMinEnergyPredicted (Λ := Λ) A N =
      -(2 : ℂ) *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1) := by
  unfold bipartiteToyMinEnergyPredicted
  rw [h]
  ring

end LatticeSystem.Quantum
