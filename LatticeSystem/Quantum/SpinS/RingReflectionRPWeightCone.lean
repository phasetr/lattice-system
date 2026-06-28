/-
The reflection-positive trace weights form a cone, closed under cone-representable factors
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 11).

The reflection-positive trace weights (`RPTraceWeightS`) form a convex cone — closed under addition,
nonnegative scaling, and finite sums — and contain the identity (the `β = 0` trace cone).  Combined
with the cone-generator closure (`RingReflectionGibbsRP`), an RP trace weight multiplied by a
cone-representable operator is again an RP trace weight (`mul_coneRep_right`).  This is
the algebraic engine that lets the Trotter expansion of `e^{-βH}` accumulate reflection positivity
factor by factor in the Dyson–Lieb–Simon argument.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionGibbsRP

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- The zero operator is a reflection-positive trace weight. -/
theorem RPTraceWeightS.zero : RPTraceWeightS n N 0 := by
  intro A _
  change 0 ≤ ((0 * (ringReflectionThetaS n N A * A)).trace).re
  rw [zero_mul, Matrix.trace_zero, Complex.zero_re]

/-- The identity is a reflection-positive trace weight (the `β = 0` trace cone). -/
theorem RPTraceWeightS.one : RPTraceWeightS n N 1 := by
  intro A hA
  change 0 ≤ ((1 * (ringReflectionThetaS n N A * A)).trace).re
  rw [one_mul]
  exact traceFunctional_reflectionPositive n N A hA

/-- Reflection-positive trace weights are closed under addition. -/
theorem RPTraceWeightS.add {M M' : ManyBodyOpS (Fin (2 * n)) N} (hM : RPTraceWeightS n N M)
    (hM' : RPTraceWeightS n N M') : RPTraceWeightS n N (M + M') := by
  intro A hA
  change 0 ≤ (((M + M') * (ringReflectionThetaS n N A * A)).trace).re
  rw [add_mul, Matrix.trace_add, Complex.add_re]
  exact add_nonneg (hM A hA) (hM' A hA)

/-- Reflection-positive trace weights are closed under nonnegative scaling. -/
theorem RPTraceWeightS.smul_nonneg {M : ManyBodyOpS (Fin (2 * n)) N} {c : ℝ} (hc : 0 ≤ c)
    (hM : RPTraceWeightS n N M) : RPTraceWeightS n N ((c : ℂ) • M) := by
  intro A hA
  change 0 ≤ (((c : ℂ) • M * (ringReflectionThetaS n N A * A)).trace).re
  rw [smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_nonneg hc (hM A hA)

/-- Reflection-positive trace weights are closed under finite sums. -/
theorem RPTraceWeightS.sum {ι : Type*} (s : Finset ι) (f : ι → ManyBodyOpS (Fin (2 * n)) N)
    (h : ∀ i ∈ s, RPTraceWeightS n N (f i)) : RPTraceWeightS n N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using RPTraceWeightS.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **Right cone-representable closure.**  An RP trace weight multiplied on the right by a
cone-representable operator is again an RP trace weight. -/
theorem RPTraceWeightS.mul_coneRep_right {M P : ManyBodyOpS (Fin (2 * n)) N}
    (hM : RPTraceWeightS n N M) (hP : RPTraceConeRepS n N P) : RPTraceWeightS n N (M * P) := by
  obtain ⟨ι, _, C, c, hC, hc, rfl⟩ := hP
  rw [Finset.mul_sum]
  refine RPTraceWeightS.sum _ _ (fun i _ => ?_)
  rw [mul_smul_comm]
  exact (hM.mul_weightGen_right (hC i)).smul_nonneg (hc i)

end LatticeSystem.Quantum
