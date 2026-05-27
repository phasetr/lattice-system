import LatticeSystem.Quantum.SpinS.AxisSwapDegeneracy
import LatticeSystem.Quantum.SpinS.SpinHalfSpecialization
import LatticeSystem.Quantum.SpinHalfRotation.Conjugation

/-!
# The explicit spin-1/2 axis-swap unitary

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The `AxisSwapUnitaryS` interface (#3752) is made non-vacuous at `N = 1` (spin-1/2) by the
`π/2` rotation about spin-axis 1, `Û^{(1)}_{π/2}` (`spinHalfRot1 (π/2)`).  Conjugation by this
rotation fixes `Ŝ¹`, sends `Ŝ² ↦ Ŝ³` and `Ŝ³ ↦ −Ŝ²`, which is exactly the axis-`2↔3`
relabelling behind Tasaki's gauge transformation between (2.5.14) and (2.5.15).

Combined with the degeneracy-transfer corollary (#3753), this gives the **spin-1/2 milestone**:
on any finite lattice the anisotropic Hamiltonian and its axis-swapped image have equal
ground-state degeneracy.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43–44; §2.1 eq. (2.1.15).
-/

namespace LatticeSystem.Quantum

open Matrix Module

/-- Generic conjugation swap: from `A Ainv = 1` and `Ainv X A = Y`, deduce `A Y Ainv = X`.
This turns an adjoint-conjugation lemma `Û†ŜÛ = …` (with `Ainv = Û†`) into the forward form
`ÛŜÛ† = …`. -/
private theorem unitary_conj_swap {n : Type*} [Fintype n] [DecidableEq n]
    {A Ainv X Y : Matrix n n ℂ} (hAAinv : A * Ainv = 1) (h : Ainv * X * A = Y) :
    A * Y * Ainv = X := by
  have hrw : A * Y * Ainv = (A * Ainv) * X * (A * Ainv) := by rw [← h]; noncomm_ring
  rw [hrw, hAAinv, one_mul, mul_one]

/-- `Û^{(1)}_{π/2} (Û^{(1)}_{π/2})† = 1` (unitarity of the axis-1 `π/2` rotation). -/
private theorem spinHalfRot1_halfPi_mul_adjoint :
    spinHalfRot1 (Real.pi / 2) * Matrix.conjTranspose (spinHalfRot1 (Real.pi / 2)) = 1 := by
  rw [spinHalfRot1_adjoint, spinHalfRot1_mul, add_neg_cancel, spinHalfRot1_zero]

/-- **The explicit spin-1/2 axis-swap unitary**: the `π/2` rotation about spin-axis 1.
It fixes `Ŝ¹`, rotates `Ŝ² ↦ Ŝ³`, `Ŝ³ ↦ −Ŝ²` — the axis-`2↔3` swap of Theorem 2.4. -/
noncomputable def axisSwapUnitarySpinHalf : AxisSwapUnitaryS 1 where
  U := spinHalfRot1 (Real.pi / 2)
  Uinv := Matrix.conjTranspose (spinHalfRot1 (Real.pi / 2))
  U_mul_Uinv := spinHalfRot1_halfPi_mul_adjoint
  Uinv_mul_U := by
    rw [spinHalfRot1_adjoint, spinHalfRot1_mul, neg_add_cancel, spinHalfRot1_zero]
  conj_spinSOp1 := by
    rw [spinSOp1_one_eq_spinHalfOp1]
    exact unitary_conj_swap spinHalfRot1_halfPi_mul_adjoint
      (spinHalfRot1_conj_spinHalfOp1 (Real.pi / 2))
  conj_spinSOp2 := by
    rw [spinSOp2_one_eq_spinHalfOp2, spinSOp3_one_eq_spinHalfOp3]
    exact unitary_conj_swap spinHalfRot1_halfPi_mul_adjoint
      spinHalfRot1_half_pi_conj_spinHalfOp3
  conj_spinSOp3 := by
    rw [spinSOp3_one_eq_spinHalfOp3, spinSOp2_one_eq_spinHalfOp2]
    have h : Matrix.conjTranspose (spinHalfRot1 (Real.pi / 2)) * (-spinHalfOp2) *
        spinHalfRot1 (Real.pi / 2) = spinHalfOp3 := by
      rw [mul_neg, neg_mul, spinHalfRot1_half_pi_conj_spinHalfOp2]
      exact neg_neg _
    exact unitary_conj_swap spinHalfRot1_halfPi_mul_adjoint h

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 milestone**: on any finite lattice the spin-1/2 anisotropic Hamiltonian
(2.5.14) and its axis-swapped image (2.5.15) have equal `μ`-eigenspace dimension, hence equal
ground-state degeneracy. -/
theorem spinHalf_anisotropic_axisSwapped_eigenspace_finrank_eq
    (J : Λ → Λ → ℂ) (lam D μ : ℂ) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D 1)) μ) =
      finrank ℂ (End.eigenspace
        (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J lam D 1)) μ) :=
  axisSwapUnitarySpinHalf.anisotropic_axisSwapped_eigenspace_finrank_eq J lam D μ

end LatticeSystem.Quantum
