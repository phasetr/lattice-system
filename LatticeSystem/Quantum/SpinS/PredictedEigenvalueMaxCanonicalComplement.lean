import LatticeSystem.Quantum.SpinS.PredictedEigenvalueCanonicalEqSquareAdd
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueComplementEqSquareSub
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# `max(canonical, complement)` predicted `(Ŝ_tot)²` eigenvalue = `‖biw‖·(‖biw‖+1)`

The canonical predicted `(Ŝ_tot)²` eigenvalue (PR #2964):
`canonical = biw.re² + biw.re`.

The complement predicted `(Ŝ_tot)²` eigenvalue (PR #2965):
`complement = biw.re² − biw.re`.

Their **maximum** is:
`max(canonical, complement) = biw.re² + |biw.re| = ‖biw‖·(‖biw‖+1)`

**without any orientation hypothesis**, since `biw.im = 0` gives
`‖biw‖ = |biw.re|`. This is the "physical" predicted `(Ŝ_tot)²`
eigenvalue — the max over both orientations corresponds to the
correct sign of the predicted `S_tot`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max(canonical, complement)` predicted `(Ŝ_tot)²` eigenvalue
= `‖biw‖·(‖biw‖+1)`** unconditionally. The physical predicted eigenvalue
is the max over both orientations. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_norm_quad
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
                ((N : ℂ) / 2)) + 1)).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
        (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ + 1) := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_sq_add
        A N,
      bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_sq_sub
        A N]
  -- max(biw.re² + biw.re, biw.re² − biw.re) = biw.re² + |biw.re| = ‖biw‖² + ‖biw‖.
  have him : (bipartiteImbalanceWeight (Λ := Λ) A N).im = 0 :=
    bipartiteImbalanceWeight_im_zero A N
  have hnorm_eq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      |(bipartiteImbalanceWeight (Λ := Λ) A N).re| := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, him]
    simp [Real.sqrt_sq_eq_abs]
  rw [hnorm_eq]
  rcases lt_or_ge (bipartiteImbalanceWeight (Λ := Λ) A N).re 0 with hneg | hpos
  · -- biw.re < 0: complement = biw.re² − biw.re > biw.re² + biw.re = canonical.
    rw [max_eq_right (by nlinarith), abs_of_neg hneg]
    ring
  · -- biw.re ≥ 0: canonical = biw.re² + biw.re ≥ biw.re² − biw.re = complement.
    rw [max_eq_left (by nlinarith), abs_of_nonneg hpos]
    ring

end LatticeSystem.Quantum
