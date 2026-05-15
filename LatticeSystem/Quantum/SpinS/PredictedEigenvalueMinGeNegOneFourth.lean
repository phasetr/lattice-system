import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMinCanonicalComplement

/-!
# Lower bound: `min(canonical, complement) ≥ −1/4` unconditionally

PR #2967: `min(canonical, complement) = ‖biw‖·(‖biw‖−1)`.

The parabola `x ↦ x·(x−1) = x² − x` has minimum at `x = 1/2` with
value `−1/4`. Since `‖biw‖ ≥ 0` always, `‖biw‖·(‖biw‖−1) ≥ −1/4`:

  `min(canonical, complement) ≥ −1/4`   unconditionally.

This is the **tight** lower bound across all configurations and `N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Lower bound**: `min(canonical, complement) ≥ −1/4` unconditionally.
The parabola `x·(x−1)` has minimum `−1/4` at `x = 1/2`. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_min_canonical_complement_ge_neg_one_fourth
    (A : Λ → Bool) (N : ℕ) :
    -(1 / 4 : ℝ) ≤
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
                  ((N : ℂ) / 2)) + 1)).re := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_min_canonical_complement_eq_norm_quad_sub
        A N]
  -- ‖biw‖·(‖biw‖-1) ≥ -1/4 always (since x² - x + 1/4 = (x - 1/2)² ≥ 0).
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ - 1 / 2)]

end LatticeSystem.Quantum
