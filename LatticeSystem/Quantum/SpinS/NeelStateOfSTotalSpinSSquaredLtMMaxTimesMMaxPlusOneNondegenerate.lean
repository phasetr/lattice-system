import LatticeSystem.Quantum.SpinS.NeelStateOfSTotalSpinSSquaredReViaImbalanceNormSq
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLtMMaxNondegenerate

/-!
# Strict bound `<(Ŝ_tot)²>_Néel.re < m_max(m_max+1)` at non-degenerate

PR #2896 gave `(<Φ_Néel|(Ŝ_tot)²|Φ_Néel>).re = ‖biw‖² + |Λ|·N/2`.

At non-degenerate (`|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`),
PR #2889 says `‖biw‖ < |Λ|·N/2 = m_max`, so squaring gives
`‖biw‖² < m_max²`. Adding `|Λ|·N/2 = m_max`:

  `<(Ŝ_tot)²>_Néel.re < m_max² + m_max = m_max·(m_max + 1)`.

The Néel state's `(Ŝ_tot)²` expectation is strictly below the
fully-polarised ferromagnetic eigenvalue `m_max(m_max+1)` at
non-degenerate. Saturated at saturated edges (PR #2898).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Strict bound on `<(Ŝ_tot)²>_Néel.re`** at non-degenerate:
`< (|Λ|·N/2)·(|Λ|·N/2 + 1) = m_max·(m_max + 1)`. -/
theorem neelStateOfS_totalSpinSSquared_expectation_re_lt_mMax_times_mMax_plus_one_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSSquared Λ N).mulVec (neelStateOfS A N))).re <
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2 + 1) := by
  rw [neelStateOfS_totalSpinSSquared_expectation_re_via_imbalance_norm_sq]
  have hbiw_lt :=
    bipartiteImbalanceWeight_norm_lt_mMax_of_nondegenerate A N hA hAc hN
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
    norm_nonneg _
  -- |Λ| > 0 from |A| > 0.
  have hLpos : 0 < (Fintype.card Λ : ℝ) := by
    obtain ⟨x, _⟩ := Finset.card_pos.mp hA
    have : 0 < Fintype.card Λ := Fintype.card_pos_iff.mpr ⟨x⟩
    exact_mod_cast this
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hLN_pos : 0 < (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
    refine div_pos ?_ two_pos
    exact mul_pos hLpos hNpos
  have hsq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ <
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) :=
    mul_lt_mul' (le_of_lt hbiw_lt) hbiw_lt hbiw_nn hLN_pos
  nlinarith [hsq]

end LatticeSystem.Quantum
