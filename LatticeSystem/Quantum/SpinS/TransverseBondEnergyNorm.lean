/-
Operator-norm bound on the transverse bond energy
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

The transverse bond energy `Ŝ_a^{(1)} Ŝ_b^{(1)} + Ŝ_a^{(2)} Ŝ_b^{(2)}` — the per-bond f-sum-rule
oscillator strength (`= −[Ŝ_a^{(3)}, [Ŝ_a · Ŝ_b, Ŝ_a^{(3)}]]`) — has operator norm `≤ 2 N²`: each of
the two Cartesian products factorizes through the per-site norm bound `‖Ŝ^{(α)}‖ ≤ N`.  Summed over
the `O(L)` bonds adjacent to a site this bounds the oscillator strength by `O(L)`, the numerator of
the Falk–Bruch bound on the staggered order parameter.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerLocality

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Operator-norm bound on the transverse bond energy**:
`‖Ŝ_a^{(1)} Ŝ_b^{(1)} + Ŝ_a^{(2)} Ŝ_b^{(2)}‖ ≤ 2 N²`. -/
theorem transverseBondEnergy_manyBodyOperatorNormS_le (a b : Λ) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp1 N)
        + onSiteS a (spinSOp2 N) * onSiteS b (spinSOp2 N)) ≤ 2 * (N : ℝ) ^ 2 := by
  have s1a := onSiteS_spinSOp1_manyBodyOperatorNormS_le (Λ := Λ) a hN
  have s1b := onSiteS_spinSOp1_manyBodyOperatorNormS_le (Λ := Λ) b hN
  have s2a := onSiteS_spinSOp2_manyBodyOperatorNormS_le (Λ := Λ) a hN
  have s2b := onSiteS_spinSOp2_manyBodyOperatorNormS_le (Λ := Λ) b hN
  have hbound : ∀ Pa Pb : ManyBodyOpS Λ N,
      manyBodyOperatorNormS Pa ≤ (N : ℝ) → manyBodyOperatorNormS Pb ≤ (N : ℝ) →
      manyBodyOperatorNormS (Pa * Pb) ≤ (N : ℝ) * (N : ℝ) := fun Pa Pb ha hb =>
    le_trans (manyBodyOperatorNormS_mul_le Pa Pb)
      (mul_le_mul ha hb (manyBodyOperatorNormS_nonneg Pb) (Nat.cast_nonneg N))
  calc manyBodyOperatorNormS (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp1 N)
          + onSiteS a (spinSOp2 N) * onSiteS b (spinSOp2 N))
      ≤ manyBodyOperatorNormS (onSiteS a (spinSOp1 N) * onSiteS b (spinSOp1 N))
          + manyBodyOperatorNormS (onSiteS a (spinSOp2 N) * onSiteS b (spinSOp2 N)) :=
        manyBodyOperatorNormS_add_le _ _
    _ ≤ (N : ℝ) * (N : ℝ) + (N : ℝ) * (N : ℝ) :=
        add_le_add (hbound _ _ s1a s1b) (hbound _ _ s2a s2b)
    _ = 2 * (N : ℝ) ^ 2 := by ring

end LatticeSystem.Quantum
