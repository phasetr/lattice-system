import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs
import LatticeSystem.Quantum.SpinS.NeelBipartiteWeight

/-!
# `‖bipartiteImbalanceWeight A N‖ = (bipartiteImbalanceWeight A N).re`
when `|A| ≥ |¬A|`

The imbalance weight is a real number (PR #2825). When
`|A| ≥ |¬A|`, its real part is non-negative (PR #2773
`_re_nonneg_of_cardA_ge_cardNotA`), so its norm equals its real
part directly.

  `|¬A| ≤ |A| → ‖bipartiteImbalanceWeight A N‖ = (bipartiteImbalanceWeight A N).re`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Norm = real part when `|A| ≥ |¬A|`**:
`‖bipartiteImbalanceWeight A N‖ = (bipartiteImbalanceWeight A N).re`. -/
theorem bipartiteImbalanceWeight_norm_eq_re_of_cardNotA_le_cardA
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
         (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  have hre_nn := bipartiteImbalanceWeight_re_nonneg_of_cardA_ge_cardNotA A N h
  rw [bipartiteImbalanceWeight_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    Complex.ofReal_re]
  rw [bipartiteImbalanceWeight_re_eq] at hre_nn
  exact abs_of_nonneg hre_nn

end LatticeSystem.Quantum
