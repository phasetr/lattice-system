import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationGeCanonicalPredicted
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationGtCanonicalPredictedNondegenerate
import LatticeSystem.Quantum.SpinS.NeelStateOfSExpectationEqCanonicalIffUncond

/-!
# `(pmA).re < ⟨Néel⟩.re ↔ |¬A| ≥ 1 ∧ N ≥ 1`

PR #3097: `(pmA).re ≤ ⟨Néel⟩.re` unconditional.
PR #3056: strict at `|¬A| ≥ 1 ∧ N ≥ 1`.
PR #3110: equality iff `|¬A| = 0 ∨ N = 0`.

Combining:

  `(predicted_min A).re < ⟨Néel⟩.re ↔ 0 < |¬A| ∧ 0 < N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **(pmA).re < ⟨Néel⟩.re iff `|¬A| ≥ 1 ∧ N ≥ 1`** (full strict iff). -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_canonical_predicted_re_iff_nondeg
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re <
        (dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re ↔
      0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ∧ 0 < N := by
  have hge := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_ge_canonical_predicted_re
    (Λ := Λ) A N
  have heq_iff := neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_canonical_predicted_re_iff_uncond
    (Λ := Λ) A N
  constructor
  · intro hlt
    by_contra hne
    push Not at hne
    have hor : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0 ∨ N = 0 := by
      by_cases hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card
      · have : N ≤ 0 := hne hAc
        right; exact Nat.le_zero.mp this
      · left; exact Nat.le_zero.mp (Nat.not_lt.mp hAc)
    have heq := heq_iff.mpr hor
    linarith
  · intro ⟨hAc, hN⟩
    exact neelStateOfS_heisenbergToyHamiltonianS_expectation_re_gt_canonical_predicted_re
      (Λ := Λ) A N hAc hN

end LatticeSystem.Quantum
