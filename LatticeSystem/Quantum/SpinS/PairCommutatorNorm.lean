/-
Operator-norm bound on the two-site double commutator `[Ŝ_x^{(3)}, [Ĥ, Ŝ_z^{(3)}]]`
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Each summand of the f-sum-rule oscillator strength is bounded uniformly in the ring length:
`‖[Ŝ_x^{(3)}, [Ĥ, Ŝ_z^{(3)}]]‖ ≤ 4 N³`, from the commutator norm `≤ 2‖Ŝ^{(3)}‖‖[Ĥ, Ŝ_z^{(3)}]‖`
with the per-site bound `‖Ŝ^{(3)}‖ ≤ N/2` and the divergence bound `‖[Ĥ, Ŝ_z^{(3)}]‖ ≤ 4 N²`.
Combined with the off-pair vanishing this gives the `O(L)` oscillator strength.
-/
import LatticeSystem.Quantum.SpinS.RingHamiltonianCommutatorNorm

namespace LatticeSystem.Quantum

open Matrix

/-- **Operator-norm bound on the two-site double commutator**:
`‖[Ŝ_x^{(3)}, [Ĥ, Ŝ_z^{(3)}]]‖ ≤ 4 N³` on a ring of length `L ≥ 2`. -/
theorem pair_double_commutator_norm_le (L N : ℕ) (hL : 2 ≤ L) (hN : 1 ≤ N) (x z : Fin L) :
    haveI : NeZero L := ⟨by omega⟩
    manyBodyOperatorNormS (onSiteS x (spinSOp3 N)
          * (heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
            - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N)
        - (heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
            - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N)
          * onSiteS x (spinSOp3 N))
      ≤ 4 * (N : ℝ) ^ 3 := by
  haveI : NeZero L := ⟨by omega⟩
  set M := heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
    - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N with hM
  have hMnorm := heisenbergHamiltonianS_ringCoupling_commutator_onSiteS_spinSOp3_norm_le L N hL hN z
  rw [← hM] at hMnorm
  have hAnorm := onSiteS_spinSOp3_manyBodyOperatorNormS_le (Λ := Fin L) (N := N) x
  have hAnn := manyBodyOperatorNormS_nonneg (onSiteS x (spinSOp3 N) : ManyBodyOpS (Fin L) N)
  have hMnn := manyBodyOperatorNormS_nonneg M
  have hAM : manyBodyOperatorNormS (onSiteS x (spinSOp3 N) * M)
      ≤ (N : ℝ) / 2 * (4 * (N : ℝ) ^ 2) :=
    le_trans (manyBodyOperatorNormS_mul_le _ _) (mul_le_mul hAnorm hMnorm hMnn (by positivity))
  have hMA : manyBodyOperatorNormS (M * onSiteS x (spinSOp3 N))
      ≤ 4 * (N : ℝ) ^ 2 * ((N : ℝ) / 2) :=
    le_trans (manyBodyOperatorNormS_mul_le _ _) (mul_le_mul hMnorm hAnorm hAnn (by positivity))
  calc manyBodyOperatorNormS (onSiteS x (spinSOp3 N) * M - M * onSiteS x (spinSOp3 N))
      ≤ manyBodyOperatorNormS (onSiteS x (spinSOp3 N) * M)
          + manyBodyOperatorNormS (M * onSiteS x (spinSOp3 N)) := manyBodyOperatorNormS_sub_le _ _
    _ ≤ (N : ℝ) / 2 * (4 * (N : ℝ) ^ 2) + 4 * (N : ℝ) ^ 2 * ((N : ℝ) / 2) := add_le_add hAM hMA
    _ = 4 * (N : ℝ) ^ 3 := by ring

end LatticeSystem.Quantum
