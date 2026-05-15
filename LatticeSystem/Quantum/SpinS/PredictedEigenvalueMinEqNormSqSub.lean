import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMinCanonicalComplement

/-!
# `min(canonical, complement) = ‖biw‖² − ‖biw‖` unconditionally

PR #2967: `min(canonical, complement) = ‖biw‖·(‖biw‖−1)`.

Expanding: `‖biw‖·(‖biw‖−1) = ‖biw‖² − ‖biw‖`. Hence

  `min(canonical, complement) = ‖biw‖² − ‖biw‖`
  unconditionally.

Companion of PR #2979 (max = `‖biw‖² + ‖biw‖`). Together, the
expanded forms make the affine parameterisation explicit:
- `max = ‖biw‖² + ‖biw‖`
- `min = ‖biw‖² − ‖biw‖`

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`min(canonical, complement) = ‖biw‖² − ‖biw‖`** unconditionally.
Expanded form of PR #2967. Companion of PR #2979. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_min_canonical_complement_eq_norm_sq_sub
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
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ -
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_min_canonical_complement_eq_norm_quad_sub
        A N]
  ring

end LatticeSystem.Quantum
