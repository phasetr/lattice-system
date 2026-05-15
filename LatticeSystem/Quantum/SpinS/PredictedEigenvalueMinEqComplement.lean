import LatticeSystem.Quantum.SpinS.PredictedEigenvalueCanonicalEqSquareAdd
import LatticeSystem.Quantum.SpinS.PredictedEigenvalueComplementEqSquareSub
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight

/-!
# `min(canonical, complement) = complement` at proper orientation `|¬A| ≤ |A|`

PR #2964: `canonical = biw.re² + biw.re`.
PR #2965: `complement = biw.re² − biw.re`.

At proper orientation `|¬A| ≤ |A|`, `biw.re ≥ 0`, so
`complement ≤ canonical`, hence `min(canonical, complement) = complement`.

  `min(canonical, complement) = complement`   at `|¬A| ≤ |A|`.

Companion of PR #2981 (`max = canonical` at proper orientation).
Together they confirm: at proper orientation, canonical is the physical
(max) eigenvalue, complement is the "wrong" (min) one.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **`min(canonical, complement) = complement`** at proper orientation
`|¬A| ≤ |A|`. Companion of PR #2981. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_min_canonical_complement_eq_complement_of_cardNotA_le_cardA
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card) :
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
  apply min_eq_right
  have hre_nn : 0 ≤ (bipartiteImbalanceWeight (Λ := Λ) A N).re :=
    bipartiteImbalanceWeight_re_nonneg_of_cardA_ge_cardNotA A N horient
  nlinarith [hre_nn]

end LatticeSystem.Quantum
