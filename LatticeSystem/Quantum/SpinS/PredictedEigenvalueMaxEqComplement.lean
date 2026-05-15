import LatticeSystem.Quantum.SpinS.PredictedEigenvalueCanonicalEqSquareAdd
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueComplementEqSquareSub
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# `max(canonical, complement) = complement` at complement orientation `|A| ≤ |¬A|`

PR #2964: `canonical = biw.re² + biw.re`.
PR #2965: `complement = biw.re² − biw.re`.

At complement orientation `|A| ≤ |¬A|`, `biw.re ≤ 0`, so
`complement = biw.re² − biw.re ≥ biw.re² + biw.re = canonical`. Hence
`max(canonical, complement) = complement`.

  `max(canonical, complement) = complement`   at `|A| ≤ |¬A|`.

Mirror of PR #2981 (`max = canonical` at proper orientation). The
complement orientation gives the physical predicted eigenvalue at
complement orientation.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max(canonical, complement) = complement`** at complement orientation
`|A| ≤ |¬A|`. Mirror of PR #2981. The complement orientation gives the
physical predicted eigenvalue at this orientation. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_complement_of_cardA_le_cardNotA
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
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
      ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2)) + 1)).re := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_sq_add
        A N,
      bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_sq_sub
        A N]
  apply max_eq_right
  -- biw.re ≤ 0 at complement orientation: biw.re = (|A| - |¬A|)·N/2 ≤ 0 since |A| ≤ |¬A|.
  have hre_eq := bipartiteImbalanceWeight_re_eq (Λ := Λ) A N
  have horient_real : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    exact_mod_cast horient
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hre_np : (bipartiteImbalanceWeight (Λ := Λ) A N).re ≤ 0 := by
    rw [hre_eq]
    nlinarith [horient_real, hN_nn]
  nlinarith [hre_np]

end LatticeSystem.Quantum
