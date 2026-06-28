/-
Physical ring thermal averages equal DLS thermal averages of gauge-transformed observables
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 31).

The right-half gauge is a similarity transform, so it leaves the partition function invariant and
transports thermal averages: the physical ring Heisenberg canonical average of an observable `A`
equals the reflection-positive DLS canonical average of the gauge-transformed observable
`rightGauge · A · rightGaugeInv`.  This is the bridge that carries every reflection-positivity bound
on the DLS Gibbs state back to the physical ring antiferromagnet.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionGibbsGauge
import LatticeSystem.Quantum.SpinS.HeisenbergEquilibrium

namespace LatticeSystem.Quantum

open Matrix

namespace AxisTwoPiRotS

variable (G : AxisTwoPiRotS N) (n : ℕ)

/-- The trace is invariant under conjugation by the right-half gauge (a similarity transform). -/
theorem trace_rightGauge_conj (X : ManyBodyOpS (Fin (2 * n)) N) :
    (G.rightGauge n * X * G.rightGaugeInv n).trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, G.rightGaugeInv_mul_rightGauge n, Matrix.one_mul]

/-- The DLS Gibbs operator is the gauge conjugate of the physical Gibbs operator. -/
theorem thermalGibbsOpS_toHamiltonian_eq [NeZero n] (β : ℝ) :
    thermalGibbsOpS β (ringDLSDecomposition n N).toHamiltonian
      = G.rightGauge n
        * thermalGibbsOpS β (heisenbergHamiltonianS (ringCoupling (2 * n)) N)
        * G.rightGaugeInv n := by
  simp only [thermalGibbsOpS]
  exact G.exp_neg_smul_toHamiltonian_eq n β

include G in
/-- The partition function is gauge-invariant: `Z(β, toHamiltonian) = Z(β, Ĥ)`. -/
theorem thermalPartitionFnS_toHamiltonian_eq [NeZero n] (β : ℝ) :
    thermalPartitionFnS β (ringDLSDecomposition n N).toHamiltonian
      = thermalPartitionFnS β (heisenbergHamiltonianS (ringCoupling (2 * n)) N) := by
  rw [thermalPartitionFnS, thermalPartitionFnS, G.thermalGibbsOpS_toHamiltonian_eq n,
    G.trace_rightGauge_conj n]

/-- **Physical thermal averages equal DLS thermal averages of gauge-transformed observables.**  The
physical ring Heisenberg canonical average of `A` equals the DLS canonical average of
`rightGauge · A · rightGaugeInv`. -/
theorem thermalAverageReS_toHamiltonian_eq [NeZero n] (β : ℝ)
    (A : ManyBodyOpS (Fin (2 * n)) N) :
    thermalAverageReS β (ringDLSDecomposition n N).toHamiltonian
        (G.rightGauge n * A * G.rightGaugeInv n)
      = thermalAverageReS β (heisenbergHamiltonianS (ringCoupling (2 * n)) N) A := by
  rw [thermalAverageReS, thermalAverageReS, G.thermalPartitionFnS_toHamiltonian_eq n]
  congr 2
  have hop : (G.rightGauge n * A * G.rightGaugeInv n)
        * thermalGibbsOpS β (ringDLSDecomposition n N).toHamiltonian
      = G.rightGauge n
        * (A * thermalGibbsOpS β (heisenbergHamiltonianS (ringCoupling (2 * n)) N))
        * G.rightGaugeInv n := by
    rw [G.thermalGibbsOpS_toHamiltonian_eq n]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (G.rightGaugeInv n) (G.rightGauge n), G.rightGaugeInv_mul_rightGauge n,
      Matrix.one_mul]
  rw [hop, G.trace_rightGauge_conj n]

end AxisTwoPiRotS

end LatticeSystem.Quantum
