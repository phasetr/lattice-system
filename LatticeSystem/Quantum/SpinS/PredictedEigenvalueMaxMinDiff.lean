import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxCanonicalComplement
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMinCanonicalComplement

/-!
# `max − min` of canonical/complement predicted `(Ŝ_tot)²` eigenvalues = `2·‖biw‖`

PR #2966: `max(canonical, complement) = ‖biw‖·(‖biw‖+1)`.
PR #2967: `min(canonical, complement) = ‖biw‖·(‖biw‖−1)`.

Their difference:

  `max − min = ‖biw‖·(‖biw‖+1) − ‖biw‖·(‖biw‖−1) = 2·‖biw‖`

unconditionally. Companion of PR #2960 (canonical − complement = `2·biw.re`)
using `‖biw‖` instead of signed `biw.re`. Since `‖biw‖ ≥ 0`, the
max-min gap is always non-negative.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max − min` of canonical/complement predicted `(Ŝ_tot)²`
eigenvalues = `2·‖biw‖`** unconditionally. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_sub_min_eq_two_norm
    (A : Λ → Bool) (N : ℕ) :
    max
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2) -
                ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)).re
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2) -
                ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)).re -
      min
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2) -
                ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
              ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                    ((N : ℂ) / 2) -
                  ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                    ((N : ℂ) / 2)) + 1)).re
          ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2) -
                ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
              ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                    ((N : ℂ) / 2) -
                  ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                    ((N : ℂ) / 2)) + 1)).re =
      2 * ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_norm_quad
        A N,
      bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_min_canonical_complement_eq_norm_quad_sub
        A N]
  ring

end LatticeSystem.Quantum
