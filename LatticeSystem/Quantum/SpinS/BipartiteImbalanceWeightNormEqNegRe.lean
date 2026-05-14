import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight

/-!
# `‖bipartiteImbalanceWeight A N‖ = -(bipartiteImbalanceWeight A N).re`
when `|A| ≤ |¬A|`

Mirror of PR #2862: when `|A| ≤ |¬A|`, the imbalance weight has
non-positive real part, so its norm equals the negation:

  `|A| ≤ |¬A| → ‖bipartiteImbalanceWeight A N‖ = -(bipartiteImbalanceWeight A N).re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Norm = -real part when `|A| ≤ |¬A|`**:
`‖bipartiteImbalanceWeight A N‖ = -(bipartiteImbalanceWeight A N).re`. -/
theorem bipartiteImbalanceWeight_norm_eq_neg_re_of_cardA_le_cardNotA
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
         (Finset.univ.filter (fun x : Λ => (! A x) = true)).card) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      -(bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  rw [bipartiteImbalanceWeight_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    Complex.ofReal_re]
  -- Show the real-axis value is non-positive.
  have hdiff : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) ≤ 0 := by
    have : ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) ≤
        ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) := by
      exact_mod_cast h
    linarith
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have hprod : (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) -
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)) *
      ((N : ℝ) / 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hdiff hN_nn
  exact abs_of_nonpos hprod

end LatticeSystem.Quantum
