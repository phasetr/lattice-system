import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubComplementReEq

/-!
# Absolute signed difference: `|(pmA).re − (pm¬A).re| = ||A| − |¬A||·N`

PR #3021: `(predicted_min A).re − (predicted_min ¬A).re = (|A| − |¬A|)·N`.

Taking absolute values on both sides (using `|x·y| = |x|·|y|` and
non-negativity of `(N : ℝ)`):

  `|(predicted_min A).re − (predicted_min ¬A).re| = ||A| − |¬A||·N`

unconditionally. This matches the orientation-spread formula
PR #3012 (`max − min = ||A| − |¬A||·N`), giving the alternative
characterisation of the spread via the absolute value of the
signed difference of the two orientation-specific predicted min
energies.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Absolute signed difference equals spread**: `|(predicted_min A).re −
(predicted_min ¬A).re| = ||A| − |¬A||·N` unconditionally. Direct from
PR #3021 by taking absolute values. -/
theorem bipartiteToyMinEnergyPredicted_abs_sub_complement_re_eq
    (A : Λ → Bool) (N : ℕ) :
    |(bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re -
        (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re| =
      |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredicted_re_sub_complement_re_eq A N, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))]

end LatticeSystem.Quantum
