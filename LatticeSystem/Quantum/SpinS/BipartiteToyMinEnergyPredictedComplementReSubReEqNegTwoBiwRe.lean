import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergyPredictedReSubComplementReEqTwoBiwRe

/-!
# `(pm¬A).re − (pmA).re = −2 · biw.re`

Negation of PR #3159: the difference reversed. The complement
predicted-min energy minus the canonical predicted-min energy equals
the negative double imbalance-weight real part.

  `(predicted_min ¬A).re − (predicted_min A).re = −2 · biw.re
   = −(|A| − |¬A|)·N = (|¬A| − |A|)·N`

unconditionally.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **(pm¬A).re − (pmA).re = −2 · biw.re** unconditionally. Negation of PR #3159. -/
theorem bipartiteToyMinEnergyPredicted_complement_re_sub_re_eq_neg_two_biw_re
    (A : Λ → Bool) (N : ℕ) :
    (bipartiteToyMinEnergyPredicted (Λ := Λ) (fun x => ! A x) N).re -
        (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      -(2 * (bipartiteImbalanceWeight (Λ := Λ) A N).re) := by
  have h := bipartiteToyMinEnergyPredicted_re_sub_complement_re_eq_two_biw_re
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
