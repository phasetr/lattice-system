import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# Saturated-edge specialisations of the `bipartiteImbalanceWeight` norm

At the saturated edges (`|¬A| = 0` or `|A| = 0`), the
imbalance-weight norm reduces to its maximal value `|Λ|·N/2`:

  `|¬A| = 0 → ‖bipartiteImbalanceWeight A N‖ = |Λ|·N/2`,
  `|A| = 0 → ‖bipartiteImbalanceWeight A N‖ = |Λ|·N/2`.

This matches the maximum total spin `m_max = |Λ|·N/2 = |Λ|·S`
attained at the all-aligned ferromagnetic state, consistent with
Tasaki §2.5 Theorem 2.3's `||A| − |¬A||·S` formula at the
saturated limit (one sublattice empty).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- Helper: at the saturated edge `|¬A| = 0`, `|A| = |Λ|`. -/
private theorem cardA_eq_of_cardNotA_zero
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    (Finset.univ.filter (fun x : Λ => A x = true)).card =
      Fintype.card Λ := by
  classical
  have hsum : (Finset.univ.filter (fun x : Λ => A x = true)).card +
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
      Fintype.card Λ := by
    have hfilter_eq : Finset.univ.filter (fun x : Λ => (! A x) = true) =
        Finset.univ.filter (fun x : Λ => ¬ (A x = true)) := by
      congr 1; funext x; rcases A x <;> simp
    rw [hfilter_eq, ← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : Λ => A x = true)
  omega

/-- Helper: at the opposite saturated edge `|A| = 0`, `|¬A| = |Λ|`. -/
private theorem cardNotA_eq_of_cardA_zero
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
      Fintype.card Λ := by
  classical
  have hsum : (Finset.univ.filter (fun x : Λ => A x = true)).card +
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
      Fintype.card Λ := by
    have hfilter_eq : Finset.univ.filter (fun x : Λ => (! A x) = true) =
        Finset.univ.filter (fun x : Λ => ¬ (A x = true)) := by
      congr 1; funext x; rcases A x <;> simp
    rw [hfilter_eq, ← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : Λ => A x = true)
  omega

/-- **Imbalance-weight norm at `|¬A| = 0` saturated edge**:
`‖bipartiteImbalanceWeight A N‖ = |Λ|·N/2`. -/
theorem bipartiteImbalanceWeight_norm_eq_mMax_of_cardNotA_zero
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [bipartiteImbalanceWeight_norm_eq, h]
  rw [cardA_eq_of_cardNotA_zero A h]
  have hcard_nn : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) := Nat.cast_nonneg _
  rw [show ((Fintype.card Λ : ℝ) - ((0 : ℕ) : ℝ)) =
        (Fintype.card Λ : ℝ) from by push_cast; ring]
  rw [abs_of_nonneg hcard_nn]
  ring

/-- **Imbalance-weight norm at `|A| = 0` opposite saturated edge**:
`‖bipartiteImbalanceWeight A N‖ = |Λ|·N/2`. -/
theorem bipartiteImbalanceWeight_norm_eq_mMax_of_cardA_zero
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [bipartiteImbalanceWeight_norm_eq, h]
  rw [cardNotA_eq_of_cardA_zero A h]
  have hcard_nn : (0 : ℝ) ≤ (Fintype.card Λ : ℝ) := Nat.cast_nonneg _
  rw [show (((0 : ℕ) : ℝ) - (Fintype.card Λ : ℝ)) =
        -(Fintype.card Λ : ℝ) from by push_cast; ring]
  rw [abs_neg, abs_of_nonneg hcard_nn]
  ring

end LatticeSystem.Quantum
