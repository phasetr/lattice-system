import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxCanonicalComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormEqZero

/-!
# Unified max iff: `max(canonical, complement) = 0 ↔ balanced` at `N ≥ 1`

PR #2966: `max(canonical, complement) = ‖biw‖·(‖biw‖+1)`.

PR #2855: `‖biw‖ = 0 ↔ balanced` at `N ≥ 1`.

Since `‖biw‖+1 ≥ 1 > 0`, `‖biw‖·(‖biw‖+1) = 0 ↔ ‖biw‖ = 0`. Hence

  `max(canonical, complement) = 0 ↔ |A| = |¬A|`   at `N ≥ 1`.

The **physical** predicted `(Ŝ_tot)²` eigenvalue (max over orientations)
vanishes exactly at balanced sublattices — singlet `S_tot = 0`.

Complements PR #2971 (`max > 0 ↔ unbalanced`). Unifies PR #2936
(canonical = 0 at orientation) and PR #2953 (complement = 0 at
orientation) via the physical max quantity.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Unified max iff**: `max(canonical, complement) = 0 ↔ balanced**
at `N ≥ 1`. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_zero_iff_balanced
    (A : Λ → Bool) (N : ℕ) (hN : 1 ≤ N) :
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
                  ((N : ℂ) / 2)) + 1)).re = 0 ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card =
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_norm_quad
        A N]
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := norm_nonneg _
  constructor
  · intro heq
    -- ‖biw‖·(‖biw‖+1) = 0 and ‖biw‖+1 ≥ 1 > 0 ⟹ ‖biw‖ = 0.
    rcases mul_eq_zero.mp heq with h | h
    · exact (bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq (Λ := Λ) A hN).mp h
    · linarith
  · intro hbal
    have hbiw_zero : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ = 0 :=
      (bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq (Λ := Λ) A hN).mpr hbal
    rw [hbiw_zero]; ring

end LatticeSystem.Quantum
