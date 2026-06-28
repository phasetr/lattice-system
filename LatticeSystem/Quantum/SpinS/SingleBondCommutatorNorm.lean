/-
Operator-norm bound on the single-bond spin-current commutator
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

The single-bond spin current `[Ŝ_a·Ŝ_b, Ŝ_a^{(3)}] = i(Ŝ_a^{(1)}Ŝ_b^{(2)} − Ŝ_a^{(2)}Ŝ_b^{(1)})`
has operator norm `≤ 2 N²`: the imaginary unit has norm `1` and each product factorizes through
the per-site norm bound `‖Ŝ^{(α)}‖ ≤ N`.  This `O(1)` bound on each bond commutator, summed
over the two bonds incident to a site, bounds `‖[Ĥ, Ŝ_z^{(3)}]‖` by `O(1)` — the locality making
the f-sum-rule oscillator strength `O(L)`.
-/
import LatticeSystem.Quantum.SpinS.SingleBondSpinSOp3Commutator
import LatticeSystem.Quantum.SpinS.TransverseBondEnergyNorm

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Operator-norm bound on the single-bond spin current**:
`‖[Ŝ_a · Ŝ_b, Ŝ_a^{(3)}]‖ ≤ 2 N²` for `a ≠ b`. -/
theorem spinSDot_commutator_onSiteS_spinSOp3_norm_le {a b : Λ} (hab : a ≠ b) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (spinSDot a b N * onSiteS a (spinSOp3 N)
        - onSiteS a (spinSOp3 N) * spinSDot a b N) ≤ 2 * (N : ℝ) ^ 2 := by
  have s1a := onSiteS_spinSOp1_manyBodyOperatorNormS_le (Λ := Λ) a hN
  have s1b := onSiteS_spinSOp1_manyBodyOperatorNormS_le (Λ := Λ) b hN
  have s2a := onSiteS_spinSOp2_manyBodyOperatorNormS_le (Λ := Λ) a hN
  have s2b := onSiteS_spinSOp2_manyBodyOperatorNormS_le (Λ := Λ) b hN
  have hmul : ∀ Pa Pb : ManyBodyOpS Λ N,
      manyBodyOperatorNormS Pa ≤ (N : ℝ) → manyBodyOperatorNormS Pb ≤ (N : ℝ) →
      manyBodyOperatorNormS (Pa * Pb) ≤ (N : ℝ) * (N : ℝ) := fun Pa Pb ha hb =>
    le_trans (manyBodyOperatorNormS_mul_le Pa Pb)
      (mul_le_mul ha hb (manyBodyOperatorNormS_nonneg Pb) (Nat.cast_nonneg N))
  rw [spinSDot_commutator_onSiteS_spinSOp3 hab, manyBodyOperatorNormS_smul, Complex.norm_I, one_mul]
  calc manyBodyOperatorNormS (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp2 N)
          - onSiteS a (spinSOp2 N) * onSiteS b (spinSOp1 N))
      ≤ manyBodyOperatorNormS (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp2 N))
          + manyBodyOperatorNormS (onSiteS a (spinSOp2 N) * onSiteS b (spinSOp1 N)) :=
        manyBodyOperatorNormS_sub_le _ _
    _ ≤ (N : ℝ) * (N : ℝ) + (N : ℝ) * (N : ℝ) :=
        add_le_add (hmul _ _ s1a s2b) (hmul _ _ s2a s1b)
    _ = 2 * (N : ℝ) ^ 2 := by ring

end LatticeSystem.Quantum
