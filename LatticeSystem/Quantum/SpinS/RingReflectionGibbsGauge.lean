/-
The physical ring Gibbs operator gauge-conjugates to the DLS Gibbs operator
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 30).

Conjugation by the right-half gauge commutes with the matrix exponential, so the physical ring
Heisenberg Gibbs operator `exp(−β Ĥ)` and the reflection-positive DLS Gibbs operator
`exp(−β · ringDLSDecomposition.toHamiltonian)` are unitarily equivalent.  Consequently every
physical thermal average equals the DLS thermal average of the gauge-transformed observable, where
the reflection-positivity bounds apply.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionGaugeAssembly
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

namespace LatticeSystem.Quantum

open Matrix

namespace AxisTwoPiRotS

variable (G : AxisTwoPiRotS N) (n : ℕ)

/-- The right-half gauge unitary has a right inverse as well. -/
theorem rightGauge_mul_rightGaugeInv : G.rightGauge n * G.rightGaugeInv n = 1 := by
  rw [rightGauge, rightGaugeInv, manyBodyTensorS_mul]
  rw [show (fun i : Fin (2 * n) => (if n ≤ (i : ℕ) then G.U else 1)
      * (if n ≤ (i : ℕ) then G.Uinv else 1)) = fun _ => 1 from ?_]
  · exact manyBodyTensorS_one
  · funext i; split <;> simp [G.U_mul_Uinv]

/-- The right-half gauge unitary packaged as a unit of the operator ring. -/
noncomputable def rightGaugeUnit : (ManyBodyOpS (Fin (2 * n)) N)ˣ where
  val := G.rightGauge n
  inv := G.rightGaugeInv n
  val_inv := G.rightGauge_mul_rightGaugeInv n
  inv_val := G.rightGaugeInv_mul_rightGauge n

@[simp] theorem rightGaugeUnit_val :
    (G.rightGaugeUnit n : ManyBodyOpS (Fin (2 * n)) N) = G.rightGauge n := rfl

@[simp] theorem rightGaugeUnit_inv :
    (((G.rightGaugeUnit n)⁻¹ : (ManyBodyOpS (Fin (2 * n)) N)ˣ) : ManyBodyOpS (Fin (2 * n)) N)
      = G.rightGaugeInv n := rfl

/-- **The physical ring Gibbs operator gauge-conjugates to the DLS Gibbs operator.**  Since the
gauge conjugates the Hamiltonian (`rightGauge_conj_ringHamiltonian`) and conjugation commutes with
the matrix exponential, `exp(−β · toHamiltonian) = rightGauge · exp(−β Ĥ) · rightGaugeInv`. -/
theorem exp_neg_smul_toHamiltonian_eq [NeZero n] (β : ℝ) :
    NormedSpace.exp ((-(β : ℂ)) • (ringDLSDecomposition n N).toHamiltonian)
      = G.rightGauge n
        * NormedSpace.exp ((-(β : ℂ)) • heisenbergHamiltonianS (ringCoupling (2 * n)) N)
        * G.rightGaugeInv n := by
  rw [show (-(β : ℂ)) • (ringDLSDecomposition n N).toHamiltonian
      = G.rightGauge n * ((-(β : ℂ)) • heisenbergHamiltonianS (ringCoupling (2 * n)) N)
        * G.rightGaugeInv n by
    rw [mul_smul_comm, smul_mul_assoc, G.rightGauge_conj_ringHamiltonian n]]
  have h := Matrix.exp_units_conj (G.rightGaugeUnit n)
    ((-(β : ℂ)) • heisenbergHamiltonianS (ringCoupling (2 * n)) N)
  simpa only [rightGaugeUnit_val, rightGaugeUnit_inv] using h

end AxisTwoPiRotS

end LatticeSystem.Quantum
