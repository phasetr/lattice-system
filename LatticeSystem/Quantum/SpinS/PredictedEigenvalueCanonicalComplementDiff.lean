import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceRe
import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceReComplement

/-!
# Canonical − complement predicted `(Ŝ_tot)²` eigenvalue difference: `2·biw.re`

The canonical predicted `(Ŝ_tot)²` eigenvalue (PR #2932):
`canonical_eigenvalue.re = biw.re·(biw.re + 1)`.

The complement predicted `(Ŝ_tot)²` eigenvalue (PR #2955):
`complement_eigenvalue.re = biw.re·(biw.re − 1)`.

Their difference:

  `canonical_eigenvalue.re − complement_eigenvalue.re
     = biw.re·(biw.re + 1) − biw.re·(biw.re − 1) = 2·biw.re`

**without any orientation hypothesis**. The canonical-complement
eigenvalue gap is exactly `2·biw.re` — twice the signed imbalance.
At balanced (`biw.re = 0`), the two orientations agree; otherwise
they differ by twice the magnetization-density signed-imbalance.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Canonical − complement predicted `(Ŝ_tot)²` eigenvalue difference**:
`= 2·biw.re` unconditionally. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_sub_complement_eq_two_imbalance_re
    (A : Λ → Bool) (N : ℕ) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
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
                  ((N : ℂ) / 2)) + 1)).re =
      2 * (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad
        A N,
      bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad_signed
        A N]
  ring

end LatticeSystem.Quantum
