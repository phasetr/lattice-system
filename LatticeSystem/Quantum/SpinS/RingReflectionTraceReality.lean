/-
The reflection map conjugates the trace, and the RP form has a real diagonal
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 33).

The reflection map `θ` conjugates the trace, `Tr(θ X) = conj(Tr X)` (reindex the diagonal by the
involutive site reflection).  Consequently, for a reflection-invariant weight `M` (`θ M = M`) and a
left-supported `A`, the diagonal value `Tr(M · θA · A)` of the reflection-positivity form is real:
`θ(M·θA·A) = M·θA·A` because `θ` is a `*`-homomorphism, `θ² = id`, and a left-supported `A` commutes
with `θA` (which lives on the right half).  Together with `rpTraceWeight_cauchySchwarz`, this shows
`(A, B) ↦ Tr(M·θA·B)` is a genuine positive-semidefinite form with real diagonal.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionCauchySchwarz

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **The reflection map conjugates the trace**: `Tr(θ X) = conj(Tr X)`, by reindexing the diagonal
sum along the involutive configuration reflection. -/
theorem ringReflectionThetaS_trace (X : ManyBodyOpS (Fin (2 * n)) N) :
    (ringReflectionThetaS n N X).trace = starRingEnd ℂ X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, ringReflectionThetaS_apply, map_sum]
  exact Fintype.sum_equiv (ringConfigReflectEquiv n N)
    (fun σ => starRingEnd ℂ (X (ringConfigReflect n N σ) (ringConfigReflect n N σ)))
    (fun μ => starRingEnd ℂ (X μ μ)) (fun σ => by rw [ringConfigReflectEquiv_apply])

/-- **The reflection-positivity form has a real diagonal.**  For a reflection-invariant weight `M`
(`θ M = M`) and left-supported `A`, the diagonal value `Tr(M · θA · A)` is real. -/
theorem rpForm_diag_im_zero {M A : ManyBodyOpS (Fin (2 * n)) N}
    (hM : ringReflectionThetaS n N M = M) (hA : SupportedOnLeftS n N A) :
    (M * (ringReflectionThetaS n N A * A)).trace.im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← ringReflectionThetaS_trace]
  congr 1
  rw [ringReflectionThetaS_mul, ringReflectionThetaS_mul, ringReflectionThetaS_involutive n N A,
    hM, hA.mul_theta_comm hA]

end LatticeSystem.Quantum
