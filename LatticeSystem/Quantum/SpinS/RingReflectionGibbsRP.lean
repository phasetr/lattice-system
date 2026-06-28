/-
Closure of reflection-positive trace weights under cone generators
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 10).

The Dyson–Lieb–Simon Gibbs reflection-positivity argument expands `e^{-βH}` into a Trotter product
of `θ(L)·L`-type generators (`L` left-supported) and interaction exponentials.  The naive
"conjugation" closure `M ↦ L · M · θ(L)` does *not* preserve reflection positivity (the homomorphism
order `θ(LA) = θ(L)θ(A)` clashes with the test operator `B = AL` since left-supported operators do
not commute).  The correct closure multiplies an RP trace weight by a **cone generator** `θ(L)·L`:

* `RPTraceWeightS.mul_weightGen_right` — `M · (θ(L)·L)` is RP, by substituting the test operator
  `A ↦ L·A` (using `L·θ(A) = θ(A)·L` and `θ(L)·θ(A) = θ(L·A)`).
* `RPTraceWeightS.weightGen_mul_left` — `(θ(L)·L) · M` is RP, by substituting `A ↦ A·L`.

These are the kinetic-factor building blocks of the full Gibbs reflection positivity.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionGibbsCone

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Right cone-generator closure.**  If `M` is a reflection-positive trace weight and `L` is
left-supported, then `M · (θ(L)·L)` is a reflection-positive trace weight.  (Substitute the test
operator `A ↦ L·A`.) -/
theorem RPTraceWeightS.mul_weightGen_right {M L : ManyBodyOpS (Fin (2 * n)) N}
    (hM : RPTraceWeightS n N M) (hL : SupportedOnLeftS n N L) :
    RPTraceWeightS n N (M * (ringReflectionThetaS n N L * L)) := by
  intro A hA
  have key : (M * (ringReflectionThetaS n N L * L)) * (ringReflectionThetaS n N A * A)
      = M * (ringReflectionThetaS n N (L * A) * (L * A)) := by
    rw [ringReflectionThetaS_mul,
      show (M * (ringReflectionThetaS n N L * L)) * (ringReflectionThetaS n N A * A)
          = M * (ringReflectionThetaS n N L * (L * ringReflectionThetaS n N A) * A) by
        simp only [mul_assoc],
      hL.mul_theta_comm hA]
    simp only [mul_assoc]
  change 0 ≤ ((M * (ringReflectionThetaS n N L * L)) * (ringReflectionThetaS n N A * A)).trace.re
  rw [key]
  exact hM (L * A) (hL.mul hA)

/-- **Left cone-generator closure.**  If `M` is a reflection-positive trace weight and `L` is
left-supported, then `(θ(L)·L) · M` is a reflection-positive trace weight.  (Substitute the test
operator `A ↦ A·L`.) -/
theorem RPTraceWeightS.weightGen_mul_left {M L : ManyBodyOpS (Fin (2 * n)) N}
    (hM : RPTraceWeightS n N M) (hL : SupportedOnLeftS n N L) :
    RPTraceWeightS n N ((ringReflectionThetaS n N L * L) * M) := by
  intro A hA
  have hop : (ringReflectionThetaS n N A * A) * (ringReflectionThetaS n N L * L)
      = ringReflectionThetaS n N (A * L) * (A * L) := by
    rw [ringReflectionThetaS_mul,
      show (ringReflectionThetaS n N A * A) * (ringReflectionThetaS n N L * L)
          = ringReflectionThetaS n N A * (A * ringReflectionThetaS n N L) * L by
        simp only [mul_assoc],
      hA.mul_theta_comm hL]
    simp only [mul_assoc]
  have key : (((ringReflectionThetaS n N L * L) * M) * (ringReflectionThetaS n N A * A)).trace
      = (M * (ringReflectionThetaS n N (A * L) * (A * L))).trace := by
    rw [mul_assoc, Matrix.trace_mul_comm (ringReflectionThetaS n N L * L)
        (M * (ringReflectionThetaS n N A * A)), mul_assoc, hop]
  change 0 ≤ (((ringReflectionThetaS n N L * L) * M) * (ringReflectionThetaS n N A * A)).trace.re
  rw [key]
  exact hM (A * L) (hA.mul hL)

end LatticeSystem.Quantum
