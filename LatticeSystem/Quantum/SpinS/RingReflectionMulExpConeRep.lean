/-
An RP trace weight absorbs the exponential of a cone-representable operator
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 13).

The interaction Gibbs factor `e^{βD/m}` (with `D` cone-representable) is the exponential of a
cone-representable operator.  Multiplying a reflection-positive trace weight `M` on the right by
such an exponential preserves reflection positivity: `M · exp P` is an RP trace weight whenever `M`
is an RP trace weight and `P` is cone-representable.  The proof multiplies `M` by the
cone-representable partial sums `∑_{k<m} (k!)⁻¹ Pᵏ` (each `M · (partial sum)` is RP by
`mul_coneRep_right`) and passes to the limit (`M · exp P` is the limit by continuity of left
multiplication, then `RPTraceWeightS.tendsto`).  Together with the kinetic factor
(`RingReflectionKineticConeRep`) this lets the Trotter expansion of `e^{-βH}` consume both factors.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionRPWeightCone
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix.Normed

namespace LatticeSystem.Quantum

open Matrix Filter Topology

open scoped Matrix.Norms.Operator

variable {n N : ℕ}

/-- **The exponential partial sums converge to `exp P`.**  The partial sums
`∑_{k<r} (k!)⁻¹ • Pᵏ` tend to `exp P` in the finite-dimensional operator topology, by
`NormedSpace.exp_eq_tsum` and summability of the exponential series.  Extracted (in this
operator-scope module with a clean import closure) so both `RPTraceWeightS.mul_exp_coneRep_right`
and the two-field reflection Cauchy–Schwarz double limit (Tasaki (4.1.51), pp. 89–93; DLS 1978 §2–3)
consume the same convergence — the latter file's heavier import closure makes the ambient
`CompleteSpace` instance resolution diverge, so it reuses this rather than reproving it. -/
theorem expSeriesPartialSum_tendsto (P : ManyBodyOpS (Fin (2 * n)) N) :
    Filter.Tendsto (fun r => ∑ k ∈ Finset.range r, ((Nat.factorial k : ℂ))⁻¹ • P ^ k)
      Filter.atTop (𝓝 (NormedSpace.exp P)) := by
  haveI : CompleteSpace (ManyBodyOpS (Fin (2 * n)) N) :=
    FiniteDimensional.complete ℂ (ManyBodyOpS (Fin (2 * n)) N)
  rw [congrFun (NormedSpace.exp_eq_tsum ℂ) P]
  exact (NormedSpace.expSeries_summable' (𝕂 := ℂ) P).hasSum.tendsto_sum_nat

/-- **An RP trace weight absorbs the exponential of a cone-representable operator.**  If `M` is a
reflection-positive trace weight and `P` is cone-representable, then `M · exp P` is a
reflection-positive trace weight. -/
theorem RPTraceWeightS.mul_exp_coneRep_right {M P : ManyBodyOpS (Fin (2 * n)) N}
    (hM : RPTraceWeightS n N M) (hP : RPTraceConeRepS n N P) :
    RPTraceWeightS n N (M * NormedSpace.exp P) := by
  -- each `M · (partial sum)` is an RP trace weight (the partial sum is cone-representable)
  have hSm : ∀ m, RPTraceWeightS n N
      (M * ∑ k ∈ Finset.range m, ((Nat.factorial k : ℂ))⁻¹ • P ^ k) :=
    fun m => hM.mul_coneRep_right (hP.expSeriesPartialSum m)
  -- the partial sums converge to `M · exp P`
  have hlim : Filter.Tendsto
      (fun m => M * ∑ k ∈ Finset.range m, ((Nat.factorial k : ℂ))⁻¹ • P ^ k)
      Filter.atTop (𝓝 (M * NormedSpace.exp P)) :=
    ((continuous_const.mul continuous_id).tendsto (NormedSpace.exp P)).comp
      (expSeriesPartialSum_tendsto P)
  exact RPTraceWeightS.tendsto hSm hlim

end LatticeSystem.Quantum
