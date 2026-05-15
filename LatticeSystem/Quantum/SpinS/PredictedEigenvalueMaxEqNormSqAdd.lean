import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxCanonicalComplement

/-!
# `max(canonical, complement) = ‖biw‖² + ‖biw‖` unconditionally

PR #2966: `max(canonical, complement) = ‖biw‖·(‖biw‖+1)`.

Expanding: `‖biw‖·(‖biw‖+1) = ‖biw‖² + ‖biw‖`. Hence

  `max(canonical, complement) = ‖biw‖² + ‖biw‖`
  unconditionally.

Expanded polynomial form of PR #2966, convenient for `nlinarith` and
arithmetic manipulations.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max(canonical, complement) = ‖biw‖² + ‖biw‖`** unconditionally.
Expanded form of PR #2966. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_norm_sq_add
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
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_norm_quad
        A N]
  ring

end LatticeSystem.Quantum
