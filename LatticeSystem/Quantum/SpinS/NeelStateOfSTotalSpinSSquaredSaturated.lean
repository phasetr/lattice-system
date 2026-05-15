import LatticeSystem.Quantum.SpinS.NeelStateOfSTotalSpinSSquaredReViaImbalanceNormSq
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormSaturated

/-!
# Saturated-case Néel `(Ŝ_tot)²` expectation: `m_max·(m_max + 1)`

PR #2896 gave the form

  `(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = ‖biw‖² + |Λ|·N/2`.

At a saturated edge (`|¬A| = 0` or `|A| = 0`), the imbalance norm
attains its maximum (PR #2851 / #2852,
`bipartiteImbalanceWeight_norm_eq_mMax_of_cardNotA_zero`):

  `‖biw‖ = |Λ|·N/2 = m_max`.

Substituting, the expectation collapses to

  `(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = m_max·(m_max + 1)`

(written `(|Λ|·N/2)·(|Λ|·N/2 + 1)` here). This is exactly the
`S_tot·(S_tot + 1)` Casimir eigenvalue at `S_tot = m_max`, i.e.
the Néel state at saturated edges is a `(Ŝ_tot)²` eigenvector at
the **fully-polarised ferromagnetic** maximum-spin eigenvalue.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Saturated `|¬A| = 0` Néel `(Ŝ_tot)²` expectation =
`m_max·(m_max + 1)`**: at `|¬A| = 0`,
`(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = (|Λ|·N/2)·(|Λ|·N/2 + 1)`. -/
theorem neelStateOfS_totalSpinSSquared_expectation_re_saturated_cardNotA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N))).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
          ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) := by
  rw [neelStateOfS_totalSpinSSquared_expectation_re_via_imbalance_norm_sq]
  rw [bipartiteImbalanceWeight_norm_eq_mMax_of_cardNotA_zero A N h]
  ring

/-- **Saturated `|A| = 0` Néel `(Ŝ_tot)²` expectation =
`m_max·(m_max + 1)`**: at `|A| = 0`,
`(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = (|Λ|·N/2)·(|Λ|·N/2 + 1)`. -/
theorem neelStateOfS_totalSpinSSquared_expectation_re_saturated_cardA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N))).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
          ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) := by
  rw [neelStateOfS_totalSpinSSquared_expectation_re_via_imbalance_norm_sq]
  rw [bipartiteImbalanceWeight_norm_eq_mMax_of_cardA_zero A N h]
  ring

end LatticeSystem.Quantum
