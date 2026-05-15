import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# Positive form of `‖bipartiteImbalanceWeight A N‖` at `|A| ≥ |¬A|`

PR #2826 expressed the norm as `||A| − |¬A||·N/2`. In the case
`|A| ≥ |¬A|`, the absolute value drops and we get:

  `|¬A| ≤ |A| → ‖bipartiteImbalanceWeight A N‖
                = (|A| − |¬A|)·N/2`.

Mirror at `|A| ≤ |¬A|`:

  `|A| ≤ |¬A| → ‖bipartiteImbalanceWeight A N‖
                = (|¬A| − |A|)·N/2`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Positive form at `|A| ≥ |¬A|`**:
`‖bipartiteImbalanceWeight A N‖ = (|A| − |¬A|)·N/2`. -/
theorem bipartiteImbalanceWeight_norm_eq_diff_of_cardNotA_le_cardA
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
         (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
        ((N : ℝ) / 2) := by
  rw [bipartiteImbalanceWeight_norm_eq]
  have hdiff : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
    have : ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≤
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
      by exact_mod_cast h
    linarith
  rw [abs_of_nonneg hdiff]

/-- **Positive form at `|A| ≤ |¬A|`**:
`‖bipartiteImbalanceWeight A N‖ = (|¬A| − |A|)·N/2`. -/
theorem bipartiteImbalanceWeight_norm_eq_diff_complement_of_cardA_le_cardNotA
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)) *
        ((N : ℝ) / 2) := by
  rw [bipartiteImbalanceWeight_norm_eq]
  have hdiff :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≤ 0 := by
    have : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≤
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
      by exact_mod_cast h
    linarith
  rw [abs_of_nonpos hdiff]
  ring

end LatticeSystem.Quantum
