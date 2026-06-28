/-
Operator-norm bound on the ring spin-current divergence `[Ĥ, Ŝ_z^{(3)}]`
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Because `[Ĥ, Ŝ_z^{(3)}]` localizes to the two bonds incident to `z`, its operator norm is `O(1)`
(independent of the ring length): `‖[Ĥ, Ŝ_z^{(3)}]‖ ≤ 4 N²`, the sum of the two single-bond
spin-current norms.  This length-independent bound is the locality that turns the f-sum-rule
oscillator strength `⟨Φ, [Ô, [Ĥ, Ô]] Φ⟩` into an `O(L)` quantity (one `O(1)` contribution per site).
-/
import LatticeSystem.Quantum.SpinS.RingHamiltonianCommutatorClosed
import LatticeSystem.Quantum.SpinS.SingleBondCommutatorNorm

namespace LatticeSystem.Quantum

open Matrix

/-- **Operator-norm bound on the ring spin-current divergence**: `‖[Ĥ, Ŝ_z^{(3)}]‖ ≤ 4 N²` on a ring
of length `L ≥ 2`. -/
theorem heisenbergHamiltonianS_ringCoupling_commutator_onSiteS_spinSOp3_norm_le (L N : ℕ)
    (hL : 2 ≤ L) (hN : 1 ≤ N) (z : Fin L) :
    haveI : NeZero L := ⟨by omega⟩
    manyBodyOperatorNormS (heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
        - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N)
      ≤ 4 * (N : ℝ) ^ 2 := by
  haveI : NeZero L := ⟨by omega⟩
  rw [heisenbergHamiltonianS_ringCoupling_commutator_onSiteS_spinSOp3_closed L N hL z]
  -- backward bond: rewrite to the left-endpoint form via `spinSDot_comm`
  have hzp : z ≠ (finRotate L).symm z := fun h =>
    finRotate_ne_self hL z (by
      have hc := congrArg (finRotate L) h
      rwa [Equiv.apply_symm_apply] at hc)
  have hfwd := spinSDot_commutator_onSiteS_spinSOp3_norm_le (a := z) (b := finRotate L z)
    (Λ := Fin L) (finRotate_ne_self hL z).symm hN
  have hbwd := spinSDot_commutator_onSiteS_spinSOp3_norm_le (a := z) (b := (finRotate L).symm z)
    (Λ := Fin L) hzp hN
  rw [spinSDot_comm ((finRotate L).symm z) z]
  calc manyBodyOperatorNormS _
      ≤ manyBodyOperatorNormS (spinSDot z (finRotate L z) N * onSiteS z (spinSOp3 N)
            - onSiteS z (spinSOp3 N) * spinSDot z (finRotate L z) N)
          + manyBodyOperatorNormS (spinSDot z ((finRotate L).symm z) N * onSiteS z (spinSOp3 N)
            - onSiteS z (spinSOp3 N) * spinSDot z ((finRotate L).symm z) N) :=
        manyBodyOperatorNormS_add_le _ _
    _ ≤ 2 * (N : ℝ) ^ 2 + 2 * (N : ℝ) ^ 2 := add_le_add hfwd hbwd
    _ = 4 * (N : ℝ) ^ 2 := by ring

end LatticeSystem.Quantum
