import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyComplement

/-!
# Sublattice-swap symmetric predicted toy-Hamiltonian min energy

The signed-difference formula
`bipartiteToyMinEnergyPredicted A N := (s_A − s_B)(s_A − s_B + 1)
− s_A(s_A+1) − s_B(s_B+1)` (PR #2778) is asymmetric in `A` and
`¬A`: it matches the Tasaki §2.5 Theorem 2.3 prediction only in
the orientation `|A| ≥ |¬A|`. The orientation gap is
`(|A| − |¬A|)·N` (PR #2780).

This file packages the **sublattice-swap symmetric form**:

  `bipartiteToyMinEnergyPredictedSymm A N
     := −|A|·|¬A|·N²/2 − min(|A|, |¬A|)·N`,

equal to `bipartiteToyMinEnergyPredicted A N` exactly when
`|A| ≥ |¬A|`, and to `bipartiteToyMinEnergyPredicted (¬A) N`
when `|¬A| ≥ |A|`. This is the true Tasaki §2.5 Theorem 2.3
prediction for the toy-Hamiltonian ground-state energy,
independent of the orientation chosen for the bipartite labeling.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] {N : ℕ}

/-- **Sublattice-swap symmetric predicted toy-Hamiltonian min
energy**: `−|A|·|¬A|·N²/2 − min(|A|, |¬A|)·N`. This is the true
Tasaki §2.5 Theorem 2.3 prediction, independent of the choice of
which sublattice is labeled `A` vs `¬A`. -/
noncomputable def bipartiteToyMinEnergyPredictedSymm
    (A : Λ → Bool) (N : ℕ) : ℂ :=
  -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
      ((N : ℂ) * (N : ℂ)) / 2) -
    ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
      (N : ℂ))

/-- **Equality with the signed-difference formula when `|¬A| ≤ |A|`**:
when the original orientation has the larger sublattice (or equal),
the symmetric form coincides with PR #2778's signed version. -/
theorem bipartiteToyMinEnergyPredictedSymm_eq_predicted_of_cardNotA_le_cardA
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
         (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N =
      bipartiteToyMinEnergyPredicted (Λ := Λ) A N := by
  unfold bipartiteToyMinEnergyPredictedSymm
  rw [bipartiteToyMinEnergyPredicted_eq_simplified]
  simp only [Nat.min_eq_right h]

/-- **Equality with the complement-orientation signed-difference
formula when `|A| ≤ |¬A|`**: when the complement orientation has
the larger sublattice (or equal), the symmetric form coincides
with PR #2778's signed version applied to `¬A`. -/
theorem bipartiteToyMinEnergyPredictedSymm_eq_complement_predicted_of_cardA_le_cardNotA
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N =
      bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N := by
  unfold bipartiteToyMinEnergyPredictedSymm
  rw [bipartiteToyMinEnergyPredicted_eq_simplified (fun x => ! A x) N]
  -- Reduce `card {!(!A x)}` = `card {A x}` at the filter level.
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  simp only [Nat.min_eq_left h]
  ring

/-- **Sublattice-swap invariance**: the symmetric form is invariant
under the orientation flip `A ↔ ¬A`:

  `bipartiteToyMinEnergyPredictedSymm (¬A) N
     = bipartiteToyMinEnergyPredictedSymm A N`. -/
theorem bipartiteToyMinEnergyPredictedSymm_complement
    (A : Λ → Bool) (N : ℕ) :
    bipartiteToyMinEnergyPredictedSymm (Λ := Λ) (fun x => ! A x) N =
      bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N := by
  unfold bipartiteToyMinEnergyPredictedSymm
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  simp only [Nat.min_comm]
  ring

end LatticeSystem.Quantum
