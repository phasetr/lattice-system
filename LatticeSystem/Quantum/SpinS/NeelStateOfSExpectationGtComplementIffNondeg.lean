import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationGeComplementPredicted
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationGtComplementPredictedNondegenerate
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationEqComplementIffUncond

/-!
# `(pm¬A).re < ⟨Néel⟩.re ↔ |A| ≥ 1 ∧ N ≥ 1`

Mirror of PR #3114 for complement.

PR #3098: `(pm¬A).re ≤ ⟨Néel⟩.re` unconditional.
PR #3057: strict at `|A| ≥ 1 ∧ N ≥ 1`.
PR #3111: equality iff `|A| = 0 ∨ N = 0`.

  `(predicted_min ¬A).re < ⟨Néel⟩.re ↔ 0 < |A| ∧ 0 < N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **(pm¬A).re < ⟨Néel⟩.re iff `|A| ≥ 1 ∧ N ≥ 1`** (full strict iff). Mirror of PR #3114. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_complement_predicted_re_iff_nondeg
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re <
        (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ↔
      0 < (Finset.univ.filter (fun x : Λ => A x = true)).card ∧ 0 < N := by
  have hge := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_ge_complement_predicted_re
    (Λ := Λ) A N
  have heq_iff := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_complement_predicted_re_iff_uncond
    (Λ := Λ) A N
  constructor
  · intro hlt
    by_contra hne
    push Not at hne
    have hor : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0 ∨ N = 0 := by
      by_cases hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card
      · have : N ≤ 0 := hne hA
        right; exact Nat.le_zero.mp this
      · left; exact Nat.le_zero.mp (Nat.not_lt.mp hA)
    have heq := heq_iff.mpr hor
    linarith
  · intro ⟨hA, hN⟩
    exact neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_complement_predicted_re
      (Λ := Λ) A N hA hN

end LatticeSystem.Quantum
