import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmNorm

/-!
# Balanced-case norm of `bipartiteToyMinEnergyPredictedSymm`

PR #2848 proved
`‖bipartiteToyMinEnergyPredictedSymm A N‖ = |A|·|¬A|·N²/2 + min(|A|, |¬A|)·N`.

In the balanced case `|A| = |¬A|`, this simplifies to

  `‖bipartiteToyMinEnergyPredictedSymm A N‖ = |A|²·N²/2 + |A|·N`,

since `min(|A|, |¬A|) = |A|`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Balanced-case symm-energy norm**: when `|A| = |¬A|`,
`‖bipartiteToyMinEnergyPredictedSymm A N‖ = |A|²·N²/2 + |A|·N`. -/
theorem bipartiteToyMinEnergyPredictedSymm_norm_eq_balanced_form_of_card_eq
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card =
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    ‖bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N‖ =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 2 +
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          (N : ℝ) := by
  rw [bipartiteToyMinEnergyPredictedSymm_norm_eq]
  rw [show
    min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
    ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) from by
      rw [h]; simp]
  rw [show
    ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
    ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) from by
      rw [h]]

end LatticeSystem.Quantum
