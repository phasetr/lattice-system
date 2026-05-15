import LatticeSystem.Quantum.SpinS.PredictedEigenvalueMaxCanonicalComplement
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormEqZero

/-!
# Unified max iff: `max(canonical, complement) > 0 ↔ unbalanced` at `N ≥ 1`

PR #2966: `max(canonical, complement) = ‖biw‖·(‖biw‖+1)`.

PR #2855: `‖biw‖ = 0 ↔ balanced` at `N ≥ 1`, hence
`‖biw‖ > 0 ↔ unbalanced` (i.e., `|A| ≠ |¬A|`).

Since `‖biw‖+1 ≥ 1 > 0`, `‖biw‖·(‖biw‖+1) > 0 ↔ ‖biw‖ > 0`. Hence

  `max(canonical, complement) > 0 ↔ |A| ≠ |¬A|`   at `N ≥ 1`.

The **physical** predicted (Ŝ_tot)² eigenvalue (max over orientations)
is strictly positive iff the configuration is unbalanced. This unifies
PR #2937 (canonical pos at strict unbalanced) and PR #2954 (complement
pos at strict unbalanced) into the physical-quantity iff.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Unified max iff**: `max(canonical, complement) > 0 ↔
unbalanced** at `N ≥ 1`. The physical predicted (Ŝ_tot)² eigenvalue
is strictly positive iff `|A| ≠ |¬A|`. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_pos_iff_unbalanced
    (A : Λ → Bool) (N : ℕ) (hN : 1 ≤ N) :
    0 < max
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
                  ((N : ℂ) / 2)) + 1)).re ↔
      (Finset.univ.filter (fun x : Λ => A x = true)).card ≠
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_norm_quad
        A N]
  -- ‖biw‖·(‖biw‖+1) > 0 ↔ ‖biw‖ > 0 (since ‖biw‖+1 ≥ 1).
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := norm_nonneg _
  constructor
  · intro hpos hbal
    -- balanced ⟹ ‖biw‖ = 0 ⟹ ‖biw‖·(‖biw‖+1) = 0, contradicting > 0.
    have hbiw_zero : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ = 0 :=
      (bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq (Λ := Λ) A hN).mpr hbal
    rw [hbiw_zero] at hpos
    linarith
  · intro hne
    -- unbalanced ⟹ ‖biw‖ > 0 ⟹ ‖biw‖·(‖biw‖+1) > 0.
    have hbiw_ne : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≠ 0 := by
      intro hzero
      have : (Finset.univ.filter (fun x : Λ => A x = true)).card =
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card :=
        (bipartiteImbalanceWeight_norm_eq_zero_iff_card_eq (Λ := Λ) A hN).mp hzero
      exact hne this
    have hbiw_pos : 0 < ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
      lt_of_le_of_ne hbiw_nn (Ne.symm hbiw_ne)
    nlinarith [hbiw_pos]

end LatticeSystem.Quantum
