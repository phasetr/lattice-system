import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyProperties

/-!
# Complement-orientation identity for the predicted toy-Hamiltonian
minimum energy

The predicted minimum energy `bipartiteToyMinEnergyPredicted A N`
(PR #2778) is defined using the signed difference `(s_A - s_B)`
in the imbalance term, where `s_A = |A|·N/2, s_B = |¬A|·N/2`.
This formula correctly matches the Tasaki §2.5 Theorem 2.3
prediction only in the orientation `|A| ≥ |¬A|`; in the opposite
orientation the absolute-value form `|s_A - s_B|` is required.

This file packages the explicit relation between the
original-orientation and complement-orientation values:

  `bipartiteToyMinEnergyPredicted A N
     − bipartiteToyMinEnergyPredicted (¬A) N
     = 2 (s_A − s_B)
     = (|A| − |¬A|) · N`.

The "true" Tasaki prediction is `min(E(A), E(¬A))`, achieved by
choosing the orientation with the larger sublattice. The formula
above quantifies the gap between the two orientations.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] {N : ℕ}

/-- **Complement-orientation gap identity**:

  `bipartiteToyMinEnergyPredicted A N
     − bipartiteToyMinEnergyPredicted (¬A) N
     = (|A| − |¬A|) · N`.

Direct ring computation from
`bipartiteToyMinEnergyPredicted_eq_simplified` applied to both `A`
and `¬A`, plus `(¬¬A) = A`. -/
theorem bipartiteToyMinEnergyPredicted_sub_complement
    (A : Λ → Bool) (N : ℕ) :
    bipartiteToyMinEnergyPredicted (Λ := Λ) A N -
        bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ)) *
        (N : ℂ) := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified A N]
  rw [bipartiteToyMinEnergyPredicted_eq_simplified (fun x => ! A x) N]
  -- Replace `card {!(!A x) = true}` with `card {A x = true}` via filter
  -- congruence.
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  ring

end LatticeSystem.Quantum
