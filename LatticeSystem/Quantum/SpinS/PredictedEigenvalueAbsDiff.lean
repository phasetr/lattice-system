import LatticeSystem.Quantum.SpinS.PredictedEigenvalueCanonicalComplementDiff
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `|canonical − complement| = 2·‖biw‖` unconditionally

PR #2960: `canonical_eigenvalue.re − complement_eigenvalue.re = 2·biw.re`.

Taking absolute value:

  `|canonical − complement| = |2·biw.re| = 2·|biw.re| = 2·‖biw‖`

unconditionally, since `biw.im = 0` gives `‖biw‖ = |biw.re|`.

This is the **unsigned** form of the canonical-complement difference,
equivalent to PR #2968 (`max − min = 2·‖biw‖`) since `max − min =
|canonical − complement|` for any pair of real numbers.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`|canonical − complement| = 2·‖biw‖`** unconditionally.
Unsigned version of PR #2960. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_abs_canonical_sub_complement_eq_two_norm
    (A : Λ → Bool) (N : ℕ) :
    |((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2) -
                ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)).re -
          ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2) -
                ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
              ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                    ((N : ℂ) / 2) -
                  ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                    ((N : ℂ) / 2)) + 1)).re| =
      2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_sub_complement_eq_two_imbalance_re
        A N]
  -- |2·biw.re| = 2·|biw.re| = 2·‖biw‖ (since biw.im = 0).
  have him : (bipartiteImbalanceWeight (Λ := Λ) A N).im = 0 :=
    bipartiteImbalanceWeight_im_zero A N
  have hnorm_eq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, him]
    simp [Real.sqrt_sq_eq_abs]
  rw [hnorm_eq, abs_mul]
  simp

end LatticeSystem.Quantum
