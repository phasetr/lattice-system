import LatticeSystem.Quantum.SpinS.PredictedEigenvalueCanonicalEqSquareAdd
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueComplementEqSquareSub
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# `max(canonical, complement) = canonical` at `|¬A| ≤ |A|`

PR #2964: `canonical = biw.re² + biw.re`.
PR #2965: `complement = biw.re² − biw.re`.

At proper orientation `|¬A| ≤ |A|`, `biw.re = (|A| − |¬A|)·N/2 ≥ 0`,
so `canonical − complement = 2·biw.re ≥ 0`, hence
`max(canonical, complement) = canonical`.

Confirms that the canonical orientation gives the **physical**
predicted (Ŝ_tot)² eigenvalue exactly at proper orientation.

  `max(canonical, complement) = canonical`   at `|¬A| ≤ |A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`max(canonical, complement) = canonical`** at proper orientation
`|¬A| ≤ |A|`. The canonical orientation gives the physical predicted
eigenvalue. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_max_canonical_complement_eq_canonical_of_cardNotA_le_cardA
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card) :
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
      ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) *
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
                ((N : ℂ) / 2) -
              ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
                ((N : ℂ) / 2)) + 1)).re := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_sq_add
        A N,
      bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_sq_sub
        A N]
  -- max(biw.re² + biw.re, biw.re² − biw.re) = biw.re² + biw.re when biw.re ≥ 0.
  apply max_eq_left
  -- biw.re ≥ 0 at proper orientation.
  have hre_nn : 0 ≤ (bipartiteImbalanceWeight (Λ := Λ) A N).re :=
    bipartiteImbalanceWeight_re_nonneg_of_cardA_ge_cardNotA A N horient
  nlinarith [hre_nn]

end LatticeSystem.Quantum
