import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# Balanced-case form of `bipartiteToyMinEnergyPredictedSymm`

When `|A| = |¬A|` (balanced bipartite), the symmetric-form
predicted minimum energy simplifies to

  `bipartiteToyMinEnergyPredictedSymm A N = -|A|²·N²/2 - |A|·N`,

since `min(|A|, |¬A|) = |A|` in this case.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Balanced-case symm-predicted min energy**:
when `|A| = |¬A|`, `bipartiteToyMinEnergyPredictedSymm A N
   = -|A|²·N²/2 - |A|·N`. -/
theorem bipartiteToyMinEnergyPredictedSymm_eq_balanced_form_of_card_eq
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card =
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((N : ℂ) * (N : ℂ)) / 2) -
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          (N : ℂ) := by
  unfold bipartiteToyMinEnergyPredictedSymm
  rw [show
    ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) =
    ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) from by
      rw [h]]
  rw [show
    Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
    (Finset.univ.filter (fun x : Λ => A x = true)).card from by
      rw [h]; simp]

end LatticeSystem.Quantum
