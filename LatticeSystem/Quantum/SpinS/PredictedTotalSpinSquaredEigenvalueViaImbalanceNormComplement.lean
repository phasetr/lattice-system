import LatticeSystem.Quantum.SpinS.PredictedTotalSpinSquaredEigenvalueViaImbalanceNorm
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormComplement

/-!
# Complement-orientation predicted `(Ŝ_tot)²` eigenvalue in `‖biw‖` form

PR #2930 gave the predicted `(Ŝ_tot)²` eigenvalue identification
under the orientation `|¬A| ≤ |A|`:
`((s_A − s_B)·((s_A − s_B) + 1)).re = ‖biw‖·(‖biw‖ + 1)`.

The **complement orientation** applies the same identification
to `¬A` under `|A| ≤ |¬A|` (i.e., `|¬¬A| ≤ |¬A|`). Since
`‖bipartiteImbalanceWeight (¬A) N‖ = ‖biw A N‖` (PR #2841 norm
complement invariance), the complement form is

  `(((s_B − s_A))·((s_B − s_A) + 1)).re = ‖biw‖·(‖biw‖ + 1)`
  at `|A| ≤ |¬A|`.

Both orientations give the same predicted Casimir eigenvalue:
`‖biw‖·(‖biw‖ + 1)`, with `‖biw‖` playing the role of the
predicted total-spin magnitude `S_tot = ||A| − |¬A||·S`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Complement-orientation predicted (Ŝ_tot)² eigenvalue** at
`|A| ≤ |¬A|`: equals `‖biw‖·(‖biw‖ + 1)` (same as the original
orientation, via complement norm invariance). -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
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
  -- Apply PR #2930 with A := ¬A; the hypothesis transports via filter congruence.
  have h_eq :=
    bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
      (fun x => ! A x) N (by
        have hfilter_eq :
            Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
            Finset.univ.filter (fun x : Λ => A x = true) := by
          apply Finset.filter_congr
          intro x _
          rcases A x <;> simp
        rw [hfilter_eq]
        exact horient)
  -- h_eq : LHS_swapped = ‖biw (¬A)‖² + ‖biw (¬A)‖.
  -- ‖biw (¬A)‖ = ‖biw A‖ (PR #2841 / norm complement).
  have hfilter_eq : Finset.univ.filter (fun x : Λ => (! (! A x)) = true) =
      Finset.univ.filter (fun x : Λ => A x = true) := by
    apply Finset.filter_congr
    intro x _
    rcases A x <;> simp
  have hbiw_eq :
      ‖bipartiteImbalanceWeight (Λ := Λ) (fun x => ! A x) N‖ =
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
    bipartiteImbalanceWeight_complement_norm_eq A N
  rw [hbiw_eq] at h_eq
  rw [hfilter_eq] at h_eq
  exact h_eq

end LatticeSystem.Quantum
