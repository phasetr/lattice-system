import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedMaxAddMinComplementRe

/-!
# Arithmetic mean: `((pmA).re + (pm¬A).re) / 2 = −|A|·|¬A|·N²/2 − |Λ|·N/2`

PR #3031: `max + min = −|A|·|¬A|·N² − |Λ|·N`.

Since `max + min = (pmA).re + (pm¬A).re` (general identity), dividing
by 2:

  `((predicted_min A).re + (predicted_min ¬A).re) / 2
   = −|A|·|¬A|·N²/2 − |Λ|·N/2`

unconditionally. The **midpoint** between the two orientation-specific
predicted min energies. Equals `predictedSymm − ||A| − |¬A||·N/2`
(half the spread below the symmetric prediction).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Arithmetic mean of orientation-specific predicted min energies**:
`= −|A|·|¬A|·N²/2 − |Λ|·N/2` unconditionally. Direct from PR #3031. -/
theorem bipartiteToyMinEnergyPredicted_avg_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    ((bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re) / 2 =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
            ((N : ℝ) * (N : ℝ))) / 2 -
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  have h := bipartiteToyMinEnergyPredicted_max_add_min_complement_re_eq (Λ := Λ) A N
  have hsum : (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
      (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re =
      max (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re +
        min (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re
          (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re :=
    (max_add_min _ _).symm
  rw [hsum, h]
  ring

end LatticeSystem.Quantum
