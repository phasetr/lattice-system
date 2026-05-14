import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightComplement

/-!
# Orientation independence of the `bipartiteImbalanceWeight` norm

Combining PR #2826
(`‖bipartiteImbalanceWeight A N‖ = ||A| − |¬A||·N/2`) with PR #2841
(`bipartiteImbalanceWeight (¬A) N = -bipartiteImbalanceWeight A N`)
gives

  `‖bipartiteImbalanceWeight (fun x => ! A x) N‖
     = ‖bipartiteImbalanceWeight A N‖`,

the orientation independence of the predicted total-spin magnitude
`||A| − |¬A||·S` that appears in Tasaki §2.5 Theorem 2.3.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Orientation independence of the imbalance-weight norm**:
`‖bipartiteImbalanceWeight (¬A) N‖ = ‖bipartiteImbalanceWeight A N‖`.

Direct corollary of PR #2841 (`_complement_eq_neg`) and
`norm_neg`. -/
theorem bipartiteImbalanceWeight_complement_norm_eq :
    ‖bipartiteImbalanceWeight (Λ := Λ) (fun x => ! A x) N‖ =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  rw [bipartiteImbalanceWeight_complement_eq_neg, norm_neg]

end LatticeSystem.Quantum
