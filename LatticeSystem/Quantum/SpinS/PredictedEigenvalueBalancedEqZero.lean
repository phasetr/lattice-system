import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceRe

/-!
# Predicted `(Ŝ_tot)²` eigenvalue at balanced: `0` (singlet)

PR #2932 gave the unified signed form `((s_A − s_B)·((s_A − s_B) + 1)).re
= biw.re · (biw.re + 1)`. At `|A| = |¬A|`, `biw.re = (|A| − |¬A|)·N/2 = 0`,
so the predicted eigenvalue equals `0 · 1 = 0`.

  `predicted (Ŝ_tot)² eigenvalue = 0` at `|A| = |¬A|`.

The predicted GS at balanced sublattices has `S_tot = 0` (singlet),
consistent with Tasaki §2.5 Theorem 2.3's balanced-case prediction.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Balanced-case predicted (Ŝ_tot)² eigenvalue = 0** (singlet)**:
at `|A| = |¬A|`, the predicted eigenvalue vanishes. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_zero_of_balanced
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card =
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re = 0 := by
  rw [bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad
        A N]
  -- biw.re = (|A| - |¬A|) · N / 2 = 0 at balanced.
  have hbiw_re : (bipartiteImbalanceWeight (Λ := Λ) A N).re = 0 := by
    rw [bipartiteImbalanceWeight_re_eq]
    have h_real :
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) =
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast h
    rw [h_real]; ring
  rw [hbiw_re]
  ring

end LatticeSystem.Quantum
