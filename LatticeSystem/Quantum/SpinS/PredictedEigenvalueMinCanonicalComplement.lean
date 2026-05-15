import LatticeSystem.Quantum.SpinS.PredictedEigenvalueCanonicalEqSquareAdd
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueComplementEqSquareSub
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `min(canonical, complement)` predicted `(Ŝ_tot)²` eigenvalue = `‖biw‖·(‖biw‖−1)`

The canonical predicted `(Ŝ_tot)²` eigenvalue (PR #2964):
`canonical = biw.re² + biw.re`.

The complement predicted `(Ŝ_tot)²` eigenvalue (PR #2965):
`complement = biw.re² − biw.re`.

Their **minimum** is:
`min(canonical, complement) = biw.re² − |biw.re| = ‖biw‖·(‖biw‖−1)`

**without any orientation hypothesis**, since `biw.im = 0` gives
`‖biw‖ = |biw.re|`. Companion of PR #2966 (max).

The min corresponds to the "wrong" orientation's eigenvalue — strictly
below the physical predicted value `‖biw‖·(‖biw‖+1)`. At saturated
edges (where `‖biw‖ = m_max`), this equals `m_max·(m_max−1)`, the
"alternative" eigenvalue seen in PRs #2958/#2959.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`min(canonical, complement)` predicted `(Ŝ_tot)²` eigenvalue
= `‖biw‖·(‖biw‖−1)`** unconditionally. Companion of PR #2966 (max). -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_min_canonical_complement_eq_norm_quad_sub
    (A : Λ → Bool) (N : ℕ) :
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
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
        (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ - 1) := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_sq_add
        A N,
      bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_sq_sub
        A N]
  have him : (bipartiteImbalanceWeight (Λ := Λ) A N).im = 0 :=
    bipartiteImbalanceWeight_im_zero A N
  have hnorm_eq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, him]
    simp [Real.sqrt_sq_eq_abs]
  rw [hnorm_eq]
  rcases lt_or_ge (bipartiteImbalanceWeight (Λ := Λ) A N).re 0 with hneg | hpos
  · -- biw.re < 0: canonical = biw.re² + biw.re < biw.re² − biw.re = complement.
    rw [min_eq_left (by nlinarith), abs_of_neg hneg]
    ring
  · -- biw.re ≥ 0: complement = biw.re² − biw.re ≤ biw.re² + biw.re = canonical.
    rw [min_eq_right (by nlinarith), abs_of_nonneg hpos]
    ring

end LatticeSystem.Quantum
