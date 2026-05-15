import LatticeSystem.Quantum.SpinS.NeelStateOfSTotalSpinSOp3SqReViaImbalanceNormSq
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormLtMMaxNondegenerate

/-!
# Strict bound `<(Ŝ_tot^(3))²>_Néel.re < m_max²` at non-degenerate

PR #2904 gave `(<Φ_Néel|(Ŝ_tot^(3))²|Φ_Néel>).re = ‖biw‖²`.

At non-degenerate (`|A| ≥ 1`, `|¬A| ≥ 1`, `N ≥ 1`), PR #2889 says
`‖biw‖ < |Λ|·N/2 = m_max`, so by squaring (both sides non-negative)

  `‖biw‖² < (|Λ|·N/2)² = m_max²`,

hence

  `(<Φ_Néel|(Ŝ_tot^(3))²|Φ_Néel>).re < |Λ|²·N²/4`.

The Néel state's z-axis Casimir expectation is strictly below the
maximum `m_max²` at non-degenerate. Saturated at saturated edges.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Strict bound on `<(Ŝ_tot^(3))²>_Néel.re`** at non-degenerate:
`< |Λ|²·N²/4 = m_max²`. -/
theorem neelStateOfS_totalSpinSOp3_sq_expectation_re_lt_mMax_sq_of_nondegenerate
    (A : Λ → Bool) (N : ℕ)
    (hA : 0 < (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hAc : 0 < (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (hN : 0 < N) :
    (dotProduct (star (neelStateOfS A N))
        ((totalSpinSOp3 Λ N * totalSpinSOp3 Λ N).mulVec
          (neelStateOfS A N))).re <
      (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
        ((N : ℝ) * (N : ℝ)) / 4 := by
  rw [neelStateOfS_totalSpinSOp3_sq_expectation_re_via_imbalance_norm_sq]
  have hbiw_lt :=
    bipartiteImbalanceWeight_norm_lt_mMax_of_nondegenerate A N hA hAc hN
  have hbiw_nn : 0 ≤ ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ :=
    norm_nonneg _
  have hLN_nn : 0 ≤ (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by positivity
  -- |Λ| ≥ 1 (since |A| ≥ 1 means at least one vertex).
  have hLpos : 0 < (Fintype.card Λ : ℝ) := by
    have hAne : ((Finset.univ.filter (fun x : Λ => A x = true)) : Finset Λ).Nonempty :=
      Finset.card_pos.mp hA
    obtain ⟨x, _⟩ := hAne
    have : 0 < Fintype.card Λ := Fintype.card_pos_iff.mpr ⟨x⟩
    exact_mod_cast this
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hLN_pos : 0 < (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
    refine div_pos ?_ two_pos
    exact mul_pos hLpos hNpos
  -- Square: ‖biw‖² < (|Λ|·N/2)² = |Λ|²·N²/4.
  have hsq : ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ <
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 *
        ((Fintype.card Λ : ℝ) * (N : ℝ) / 2) :=
    mul_lt_mul' (le_of_lt hbiw_lt) hbiw_lt hbiw_nn hLN_pos
  nlinarith [hsq]

end LatticeSystem.Quantum
