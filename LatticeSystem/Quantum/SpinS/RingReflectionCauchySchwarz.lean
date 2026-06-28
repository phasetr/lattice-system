/-
The reflection-positivity Cauchy–Schwarz inequality
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 32).

A reflection-positive trace weight `M` makes `(A, B) ↦ Tr(M · θ(A) · B)` a positive-semidefinite
sesquilinear form on the left subalgebra.  Expanding `0 ≤ Re Tr(M · θ(A − tB) · (A − tB))` as a
nonnegative real quadratic in `t` and taking its discriminant gives the Cauchy–Schwarz inequality
`(Re Tr(M·θA·B) + Re Tr(M·θB·A))² ≤ 4 · Re Tr(M·θA·A) · Re Tr(M·θB·B)`.  This is the workhorse for
the Dyson–Lieb–Simon infrared bound.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionGibbsCone
import Mathlib.Algebra.QuadraticDiscriminant

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Reflection-positivity Cauchy–Schwarz.**  For a reflection-positive trace weight `M` and
left-supported `A`, `B`, the sesquilinear form `(A, B) ↦ Tr(M·θA·B)` satisfies
`(Re Tr(M·θA·B) + Re Tr(M·θB·A))² ≤ 4 · Re Tr(M·θA·A) · Re Tr(M·θB·B)`. -/
theorem rpTraceWeight_cauchySchwarz {M A B : ManyBodyOpS (Fin (2 * n)) N}
    (hM : RPTraceWeightS n N M) (hA : SupportedOnLeftS n N A) (hB : SupportedOnLeftS n N B) :
    ((M * (ringReflectionThetaS n N A * B)).trace.re
        + (M * (ringReflectionThetaS n N B * A)).trace.re) ^ 2
      ≤ 4 * (M * (ringReflectionThetaS n N A * A)).trace.re
          * (M * (ringReflectionThetaS n N B * B)).trace.re := by
  set a := (M * (ringReflectionThetaS n N B * B)).trace.re with ha
  set c := (M * (ringReflectionThetaS n N A * A)).trace.re with hc
  set p := (M * (ringReflectionThetaS n N A * B)).trace.re with hp
  set q := (M * (ringReflectionThetaS n N B * A)).trace.re with hq
  -- The nonnegative real quadratic in `t`.
  have key : ∀ t : ℝ, 0 ≤ a * (t * t) + (-(p + q)) * t + c := by
    intro t
    have hsupp : SupportedOnLeftS n N (A + (-(t : ℂ)) • B) :=
      hA.add (SupportedOnLeftS.smul (-(t : ℂ)) hB)
    have hpos := hM _ hsupp
    have hexpand : (M * (ringReflectionThetaS n N (A + (-(t : ℂ)) • B)
        * (A + (-(t : ℂ)) • B))).trace.re = a * (t * t) + (-(p + q)) * t + c := by
      rw [ringReflectionThetaS_add, ringReflectionThetaS_smul]
      simp only [map_neg, Complex.conj_ofReal, Matrix.mul_add, Matrix.add_mul,
        smul_mul_assoc, mul_smul_comm, Matrix.trace_add, Matrix.trace_smul,
        smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.neg_re,
        Complex.ofReal_re, Complex.ofReal_im, neg_mul]
      ring
    rw [hexpand] at hpos
    exact hpos
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

end LatticeSystem.Quantum
