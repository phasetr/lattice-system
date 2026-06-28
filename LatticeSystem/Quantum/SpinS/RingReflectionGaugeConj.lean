/-
Distribution laws for conjugation by the right-half gauge
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 25).

Conjugation `X ↦ rightGauge · X · rightGaugeInv` by the right-half DLS/Marshall gauge is an algebra
homomorphism: it distributes over products, sums, scalars, and finite sums.  These distribution
laws, together with the single-site conjugation `rightGauge_conj_onSiteS`, let one compute the gauge
image of any operator built from single-site operators — in particular the ring Hamiltonian.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionGauge

namespace LatticeSystem.Quantum

open Matrix

namespace AxisTwoPiRotS

variable (G : AxisTwoPiRotS N) (n : ℕ)

/-- Conjugation by the right-half gauge distributes over products. -/
theorem rightGauge_conj_mul (P Q : ManyBodyOpS (Fin (2 * n)) N) :
    G.rightGauge n * (P * Q) * G.rightGaugeInv n
      = (G.rightGauge n * P * G.rightGaugeInv n) * (G.rightGauge n * Q * G.rightGaugeInv n) := by
  rw [show (G.rightGauge n * P * G.rightGaugeInv n) * (G.rightGauge n * Q * G.rightGaugeInv n)
      = G.rightGauge n * P * (G.rightGaugeInv n * G.rightGauge n) * (Q * G.rightGaugeInv n) by
    simp only [mul_assoc], G.rightGaugeInv_mul_rightGauge]
  simp only [mul_one, mul_assoc]

/-- Conjugation by the right-half gauge distributes over sums. -/
theorem rightGauge_conj_add (P Q : ManyBodyOpS (Fin (2 * n)) N) :
    G.rightGauge n * (P + Q) * G.rightGaugeInv n
      = G.rightGauge n * P * G.rightGaugeInv n + G.rightGauge n * Q * G.rightGaugeInv n := by
  rw [mul_add, add_mul]

/-- Conjugation by the right-half gauge distributes over scalar multiples. -/
theorem rightGauge_conj_smul (c : ℂ) (P : ManyBodyOpS (Fin (2 * n)) N) :
    G.rightGauge n * (c • P) * G.rightGaugeInv n
      = c • (G.rightGauge n * P * G.rightGaugeInv n) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Conjugation by the right-half gauge distributes over finite sums. -/
theorem rightGauge_conj_sum {ι : Type*} (s : Finset ι) (f : ι → ManyBodyOpS (Fin (2 * n)) N) :
    G.rightGauge n * (∑ i ∈ s, f i) * G.rightGaugeInv n
      = ∑ i ∈ s, G.rightGauge n * f i * G.rightGaugeInv n := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, rightGauge_conj_add, ih, Finset.sum_insert ha]

end AxisTwoPiRotS

end LatticeSystem.Quantum
