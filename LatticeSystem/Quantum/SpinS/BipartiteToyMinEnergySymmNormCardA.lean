import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmNorm

/-!
# Case-specific form of `‖bipartiteToyMinEnergyPredictedSymm‖`
when `|A| ≤ |¬A|` or `|¬A| ≤ |A|`

PR #2848 expressed the symm-energy norm with the symmetric
`min(|A|, |¬A|)`. In each ordering case, `min` simplifies:

  `|A| ≤ |¬A| → ‖symm‖ = |A|·|¬A|·N²/2 + |A|·N`,
  `|¬A| ≤ |A| → ‖symm‖ = |A|·|¬A|·N²/2 + |¬A|·N`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Symm-energy norm at `|A| ≤ |¬A|`**:
`‖symm‖ = |A|·|¬A|·N²/2 + |A|·N`. -/
theorem bipartiteToyMinEnergyPredictedSymm_norm_eq_cardA_form_of_cardA_le_cardNotA
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    ‖bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N‖ =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 2 +
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredictedSymm_norm_eq]
  rw [show
    min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
    ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) from by
      apply min_eq_left
      exact_mod_cast h]

/-- **Symm-energy norm at `|¬A| ≤ |A|`**:
`‖symm‖ = |A|·|¬A|·N²/2 + |¬A|·N`. -/
theorem bipartiteToyMinEnergyPredictedSymm_norm_eq_cardNotA_form_of_cardNotA_le_cardA
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
         (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    ‖bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N‖ =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 2 +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredictedSymm_norm_eq]
  rw [show
    min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) from by
      apply min_eq_right
      exact_mod_cast h]

end LatticeSystem.Quantum
