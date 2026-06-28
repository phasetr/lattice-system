/-
Closed form of the ring Hamiltonian–`Ŝ^{(3)}` commutator (spin-current divergence)
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

On a ring of length `L ≥ 2`, the commutator `[Ĥ, Ŝ_z^{(3)}]` localizes to the two bonds incident to
`z` — the forward bond `(z, z+1)` and the backward bond `(z−1, z)`:
`[Ĥ, Ŝ_z^{(3)}] = [Ŝ_z · Ŝ_{z+1}, Ŝ_z^{(3)}] + [Ŝ_{z−1} · Ŝ_z, Ŝ_z^{(3)}]`.
This is the discrete spin-current divergence; every other bond commutes with `Ŝ_z^{(3)}`,
collapsing the bond sum to these two terms.
-/
import LatticeSystem.Quantum.SpinS.RingHamiltonianCommutatorBondSum
import LatticeSystem.Quantum.SpinS.SingleBondSpinSOp3Commutator

namespace LatticeSystem.Quantum

open Matrix

/-- The cyclic successor is not a fixed point on a ring of length `≥ 2`. -/
theorem finRotate_ne_self {L : ℕ} (hL : 2 ≤ L) (z : Fin L) : finRotate L z ≠ z := by
  haveI : NeZero L := ⟨by omega⟩
  intro h
  have hv := val_finRotate L z
  rw [h] at hv
  have hzlt := z.isLt
  rcases Nat.lt_or_ge (z.val + 1) L with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have he : z.val + 1 = L := by omega
    rw [he, Nat.mod_self] at hv; omega

/-- **Closed form of the ring Hamiltonian commutator with `Ŝ_z^{(3)}`** (spin-current divergence):
`[Ĥ, Ŝ_z^{(3)}]` is the sum of the forward- and backward-bond commutators at `z`. -/
theorem heisenbergHamiltonianS_ringCoupling_commutator_onSiteS_spinSOp3_closed (L N : ℕ)
    (hL : 2 ≤ L) (z : Fin L) :
    haveI : NeZero L := ⟨by omega⟩
    heisenbergHamiltonianS (ringCoupling L) N * onSiteS z (spinSOp3 N)
        - onSiteS z (spinSOp3 N) * heisenbergHamiltonianS (ringCoupling L) N
      = (spinSDot z (finRotate L z) N * onSiteS z (spinSOp3 N)
          - onSiteS z (spinSOp3 N) * spinSDot z (finRotate L z) N)
        + (spinSDot ((finRotate L).symm z) z N * onSiteS z (spinSOp3 N)
          - onSiteS z (spinSOp3 N) * spinSDot ((finRotate L).symm z) z N) := by
  haveI : NeZero L := ⟨by omega⟩
  rw [heisenbergHamiltonianS_ringCoupling_commutator_onSiteS_spinSOp3]
  have hzp : z ≠ (finRotate L).symm z := fun h =>
    finRotate_ne_self hL z (by
      have hc := congrArg (finRotate L) h
      rwa [Equiv.apply_symm_apply] at hc)
  have hsupp : ∀ x ∈ (Finset.univ : Finset (Fin L)),
      x ∉ ({z, (finRotate L).symm z} : Finset (Fin L)) →
      spinSDot x (finRotate L x) N * onSiteS z (spinSOp3 N)
        - onSiteS z (spinSOp3 N) * spinSDot x (finRotate L x) N = 0 := by
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    refine spinSDot_commutator_onSiteS_spinSOp3_eq_zero_of_ne (Ne.symm hx.1) ?_ N
    intro hzf
    exact hx.2 (by rw [hzf, Equiv.symm_apply_apply])
  rw [← Finset.sum_subset (Finset.subset_univ _) hsupp, Finset.sum_pair hzp,
    Equiv.apply_symm_apply]

end LatticeSystem.Quantum
