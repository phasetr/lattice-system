import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs
import LatticeSystem.Quantum.SpinS.CardSumEqFintype

/-!
# Upper bound: `‖bipartiteImbalanceWeight A N‖ ≤ |Λ|·N/2`

The predicted Theorem 2.3 spin magnitude is bounded above by
the maximum total spin `m_max = |Λ|·N/2 = |Λ|·S`:

  `‖bipartiteImbalanceWeight A N‖ ≤ |Λ|·N/2`.

Direct from `||A| − |¬A|| ≤ |A| + |¬A| = |Λ|` (PR #2870) and
PR #2826's norm formula.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Upper bound by `m_max`**:
`‖bipartiteImbalanceWeight A N‖ ≤ |Λ|·N/2`. -/
theorem bipartiteImbalanceWeight_norm_le_mMax :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ ≤
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [bipartiteImbalanceWeight_norm_eq]
  have hsum := cardA_add_cardNotA_eq_card (Λ := Λ) A
  have hsum_real :
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) +
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) =
        (Fintype.card Λ : ℝ) := by
    exact_mod_cast hsum
  have hA_nn : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) :=
    Nat.cast_nonneg _
  have hAc_nn : (0 : ℝ) ≤
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) :=
    Nat.cast_nonneg _
  have habs : |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| ≤
      (Fintype.card Λ : ℝ) := by
    rw [← hsum_real, abs_sub_le_iff]
    constructor <;> linarith
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  calc
    |((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)| *
        ((N : ℝ) / 2)
        ≤ (Fintype.card Λ : ℝ) * ((N : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_right habs hN_nn
    _ = (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by ring

end LatticeSystem.Quantum
