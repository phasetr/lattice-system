/-
The right-half gauge turns the ring Heisenberg Hamiltonian into its DLS form
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 29).

Assembling the bond conjugations: the right-half DLS/Marshall gauge conjugates the ring Heisenberg
Hamiltonian into the reflection-positive DLS Hamiltonian, `rightGauge · heisenbergHamiltonianS
(ringCoupling (2n)) · rightGaugeInv = ringDLSDecomposition.toHamiltonian`.  The left and right bond
Hamiltonians are fixed, and the two crossing bonds become the negated gauged crossing interactions.
This is the unitary equivalence bridging the physical ring antiferromagnet to its
reflection-positive form.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionUngaugedDLS
import LatticeSystem.Quantum.SpinS.RingReflectionConcreteGibbs
import LatticeSystem.Quantum.SpinS.RingReflectionCrossConj
import LatticeSystem.Quantum.SpinS.RingReflectionNonCrossConj

namespace LatticeSystem.Quantum

open Matrix

namespace AxisTwoPiRotS

variable (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n]

/-- **The right-half gauge conjugates the ring Hamiltonian into its DLS form.** -/
theorem rightGauge_conj_ringHamiltonian :
    G.rightGauge n * heisenbergHamiltonianS (ringCoupling (2 * n)) N * G.rightGaugeInv n
      = (ringDLSDecomposition n N).toHamiltonian := by
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  -- the two crossing-bond conjugations
  have hc1 : G.rightGauge n
      * spinSDot (⟨n - 1, by omega⟩ : Fin (2 * n)) (ringBondSucc n ⟨n - 1, by omega⟩) N
      * G.rightGaugeInv n = -crossBondInteractionS (⟨n - 1, by omega⟩ : Fin (2 * n)) N := by
    have hsucc : ringBondSucc n (⟨n - 1, by omega⟩ : Fin (2 * n))
        = ringReflect n (⟨n - 1, by omega⟩ : Fin (2 * n)) := by
      apply Fin.ext
      rw [ringBondSucc_val, ringReflect_val]
      change (n - 1 + 1) % (2 * n) = 2 * n - 1 - (n - 1)
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hsucc]
    exact G.rightGauge_conj_crossBond n (by change n - 1 < n; omega)
  have hc2 : G.rightGauge n
      * spinSDot (⟨2 * n - 1, by omega⟩ : Fin (2 * n)) (ringBondSucc n ⟨2 * n - 1, by omega⟩) N
      * G.rightGaugeInv n = -crossBondInteractionS (⟨0, by omega⟩ : Fin (2 * n)) N := by
    have hsucc : ringBondSucc n (⟨2 * n - 1, by omega⟩ : Fin (2 * n))
        = (⟨0, by omega⟩ : Fin (2 * n)) := by
      apply Fin.ext
      rw [ringBondSucc_val]
      change (2 * n - 1 + 1) % (2 * n) = 0
      rw [show 2 * n - 1 + 1 = 2 * n by omega, Nat.mod_self]
    have hrefl : (⟨2 * n - 1, by omega⟩ : Fin (2 * n))
        = ringReflect n (⟨0, by omega⟩ : Fin (2 * n)) := by
      apply Fin.ext; rw [ringReflect_val]; change 2 * n - 1 = 2 * n - 1 - 0; omega
    rw [hsucc, spinSDot_comm, hrefl]
    exact G.rightGauge_conj_crossBond n (by change 0 < n; omega)
  rw [heisenbergHamiltonianS_ringCoupling_ungauged_dls, rightGauge_conj_add, rightGauge_conj_add,
    rightGauge_conj_add, G.rightGauge_conj_ringLeftHamiltonian n,
    G.rightGauge_conj_theta_ringLeftHamiltonian n, hc1, hc2,
    ringDLSDecomposition_toHamiltonian]
  simp only [ringCrossingSite, Matrix.cons_val_zero, Matrix.cons_val_one]
  abel

end AxisTwoPiRotS

end LatticeSystem.Quantum
