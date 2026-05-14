import LatticeSystem.Quantum.SpinS.NeelStateMagNormEqPredicted
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormSaturated

/-!
# Néel-state magnetization norm at saturated edges = `m_max`

At the saturated edges (`|¬A| = 0` or `|A| = 0`), the Néel-state
magnetization norm reduces to the maximum `m_max = |Λ|·N/2`:

  `|¬A| = 0 → ‖magEigenvalueS (neelConfigOfS A N)‖ = |Λ|·N/2`,
  `|A| = 0 → ‖magEigenvalueS (neelConfigOfS A N)‖ = |Λ|·N/2`.

Consistent with Tasaki §2.5 Theorem 2.3 at the saturated limit:
when one sublattice is empty, the Néel configuration becomes the
all-aligned state with maximum spin `|Λ|·S`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

omit [DecidableEq Λ] in
/-- **Néel-state mag norm at `|¬A| = 0` saturated edge**:
`‖magEigenvalueS (neelConfigOfS A N)‖ = |Λ|·N/2`. -/
theorem magEigenvalueS_neelConfigOfS_norm_eq_mMax_of_cardNotA_zero
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    ‖magEigenvalueS (neelConfigOfS (Λ := Λ) A N)‖ =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [magEigenvalueS_neelConfigOfS_eq_bipartiteImbalanceWeight]
  exact bipartiteImbalanceWeight_norm_eq_mMax_of_cardNotA_zero A N h

omit [DecidableEq Λ] in
/-- **Néel-state mag norm at `|A| = 0` opposite saturated edge**:
`‖magEigenvalueS (neelConfigOfS A N)‖ = |Λ|·N/2`. -/
theorem magEigenvalueS_neelConfigOfS_norm_eq_mMax_of_cardA_zero
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    ‖magEigenvalueS (neelConfigOfS (Λ := Λ) A N)‖ =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [magEigenvalueS_neelConfigOfS_eq_bipartiteImbalanceWeight]
  exact bipartiteImbalanceWeight_norm_eq_mMax_of_cardA_zero A N h

end LatticeSystem.Quantum
