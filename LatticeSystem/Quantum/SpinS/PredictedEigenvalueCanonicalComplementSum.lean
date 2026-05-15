import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceRe
import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceReComplement

/-!
# Canonical + complement predicted `(Ŝ_tot)²` eigenvalue sum: `2·biw.re²`

The canonical predicted `(Ŝ_tot)²` eigenvalue (PR #2932):
`canonical_eigenvalue.re = biw.re·(biw.re + 1)`.

The complement predicted `(Ŝ_tot)²` eigenvalue (PR #2955):
`complement_eigenvalue.re = biw.re·(biw.re − 1)`.

Their sum:

  `canonical_eigenvalue.re + complement_eigenvalue.re
     = biw.re·(biw.re + 1) + biw.re·(biw.re − 1) = 2·biw.re²`

**without any orientation hypothesis**. Companion identity to PR #2960
(canonical − complement = `2·biw.re`). The sum is non-negative
unconditionally (since `biw.re² ≥ 0`).

Together with PR #2960 (difference), this gives the affine
parameterisation:
  `canonical_eigenvalue.re = biw.re² + biw.re`
  `complement_eigenvalue.re = biw.re² − biw.re`
of both eigenvalues as quadratic functions of `biw.re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Canonical + complement predicted (Ŝ_tot)² eigenvalue sum**:
`= 2·biw.re²` unconditionally. Companion of PR #2960 (difference). -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_add_complement_eq_two_imbalance_re_sq
    (A : Λ → Bool) (N : ℕ) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2)) + 1)).re +
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2)) *
            ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2) -
                ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)).re =
      2 * (bipartiteImbalanceWeight (Λ := Λ) A N).re *
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad
        A N,
      bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad_signed
        A N]
  ring

end LatticeSystem.Quantum
