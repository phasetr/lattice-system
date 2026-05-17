import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationSubAvg

/-!
# `2 · ⟨Néel⟩.re = (pmA).re + (pm¬A).re + |Λ|·N` unconditionally

Sum form of PR #3051 (`⟨Néel⟩.re − avg = |Λ|·N/2`). Doubling:

  `2 · ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re = (predicted_min A).re + (predicted_min ¬A).re + |Λ|·N`

unconditionally. Useful as a closed-form for `2 · ⟨Néel⟩.re` in terms
of the orientation-specific predicted-min energies and the cardinality.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`2·⟨Néel⟩.re = (pmA).re + (pm¬A).re + |Λ|·N`** unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_double_eq_pmA_add_pmNotA_add_card
    (A : Λ → Bool) (N : ℕ) :
    2 * (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re =
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re +
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re +
        (Fintype.card Λ : ℝ) * (N : ℝ) := by
  have h := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_avg_complement_re_eq
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
