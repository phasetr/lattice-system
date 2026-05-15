import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceReComplement

/-!
# Complement predicted `(Ŝ_tot)²` eigenvalue: `biw.re² − biw.re`

PR #2955 gave `complement_eigenvalue.re = biw.re·(biw.re − 1)`.
Expanding, this is `biw.re² − biw.re`. This explicit polynomial form
is convenient for `nlinarith` and arithmetic manipulations.

  `complement_eigenvalue.re = biw.re² − biw.re`
  unconditionally.

Companion of PR #2964 (canonical `= biw.re² + biw.re`). Together the
two give the symmetric affine parameterisation:
- `canonical = biw.re² + biw.re`
- `complement = biw.re² − biw.re`

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Complement predicted (Ŝ_tot)² eigenvalue = `biw.re² − biw.re`**
unconditionally. Expanded form of PR #2955. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_sq_sub
    (A : Λ → Bool) (N : ℕ) :
    ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re *
        (bipartiteImbalanceWeight (Λ := Λ) A N).re -
      (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  rw [bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad_signed
        A N]
  ring

end LatticeSystem.Quantum
