import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyComplement
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# Predicted min energy sum: `A + ¬A = -|A|·|¬A|·N² − |Λ|·N`

PR #2780-ish gave the gap identity
`bipartiteToyMinEnergyPredicted A N − bipartiteToyMinEnergyPredicted (¬A) N
  = (|A| − |¬A|)·N`. Companion sum identity:

  `bipartiteToyMinEnergyPredicted A N
     + bipartiteToyMinEnergyPredicted (¬A) N
     = −|A|·|¬A|·N² − |Λ|·N`.

Direct ring computation from `bipartiteToyMinEnergyPredicted_eq_simplified`
applied to both `A` and `¬A`, plus `(¬¬A) = A` and `|A|+|¬A| = |Λ|`.

Together with the sub identity, this gives the **affine sandwich**:
- `predicted_min_energy A + predicted_min_energy (¬A) = −|A|·|¬A|·N² − |Λ|·N` (sum).
- `predicted_min_energy A − predicted_min_energy (¬A) = (|A| − |¬A|)·N` (diff).
Hence:
- `predicted_min_energy A = −|A|·|¬A|·N²/2 − |¬A|·N` (canonical-orientation).
- `predicted_min_energy (¬A) = −|A|·|¬A|·N²/2 − |A|·N` (complement-orientation).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Complement-orientation sum identity**:
`bipartiteToyMinEnergyPredicted A N + bipartiteToyMinEnergyPredicted (¬A) N
   = −|A|·|¬A|·N² − |Λ|·N`. -/
theorem bipartiteToyMinEnergyPredicted_add_complement
    (A : Λ → Bool) (N : ℕ) :
    bipartiteToyMinEnergyPredicted (Λ := Λ) A N +
        bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) * (N : ℂ))) -
        (Fintype.card Λ : ℂ) * (N : ℂ) := by
  rw [bipartiteToyMinEnergyPredicted_eq_simplified A N]
  rw [bipartiteToyMinEnergyPredicted_eq_simplified (fun x => ! A x) N]
  -- Replace card {¬¬A} with card {A}.
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  rw [hfilter_eq]
  -- |A| + |¬A| = |Λ|.
  have hsum : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) +
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) =
      (Fintype.card Λ : ℂ) := by
    exact_mod_cast cardA_add_cardNotA_eq_card (Λ := Λ) A
  linear_combination -(N : ℂ) * hsum

end LatticeSystem.Quantum
