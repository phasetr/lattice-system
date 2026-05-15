import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceRe

/-!
# Canonical predicted `(Ŝ_tot)²` eigenvalue: `biw.re² + biw.re`

PR #2932 gave `canonical_eigenvalue.re = biw.re·(biw.re + 1)`.
Expanding, this is `biw.re² + biw.re`. This explicit polynomial form
is sometimes more convenient for `nlinarith` and arithmetic
manipulations.

  `canonical_eigenvalue.re = biw.re² + biw.re`
  unconditionally.

Together with the complement signed form (`biw.re² − biw.re`,
future companion), this gives the symmetric affine parameterisation
of both eigenvalues.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Canonical predicted (Ŝ_tot)² eigenvalue = `biw.re² + biw.re`**
unconditionally. Expanded form of PR #2932. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_sq_add
    (A : Λ → Bool) (N : ℕ) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re *
        (bipartiteImbalanceWeight (Λ := Λ) A N).re +
      (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad
        A N]
  ring

end LatticeSystem.Quantum
