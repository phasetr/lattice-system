/-
The interaction-part Gibbs exponential is a reflection-positive trace weight
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 7).

For a nonnegative finite interaction `D = t · ∑ᵢ cᵢ θ(Cᵢ)·Cᵢ` (`t, cᵢ ≥ 0`, `Cᵢ` left-supported),
the matrix exponential `exp D` is a reflection-positive trace weight.  This is the interaction
of the Gibbs weight in the Dyson–Lieb–Simon / Shastry decomposition.

The proof mounts the exponential on the trace-weight cone (`RingReflectionGibbsCone.lean`): every
partial sum `∑_{k<m} (k!)⁻¹ Dᵏ` of the exponential series is cone-representable (closure under
`smul_nonneg`, `add`, `pow`), hence a reflection-positive trace weight, and `exp D` is their limit
(`NormedSpace.expSeries_summable'.hasSum.tendsto_sum_nat`), so `RPTraceWeightS.tendsto` applies.

The matrix exponential requires the `L∞`-operator-norm Banach-algebra structure
(`open scoped Matrix.Norms.Operator`), whose topology is the entrywise (Pi) topology — the same one
underlying the trace-continuity in `RPTraceWeightS.tendsto`.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionGibbsCone
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix.Normed

namespace LatticeSystem.Quantum

open Matrix Filter Topology

open scoped Matrix.Norms.Operator

variable {n N : ℕ}

/-- **Interaction-part Gibbs reflection positivity.**  For a nonnegative finite interaction
`D = t · ∑ᵢ cᵢ θ(Cᵢ)·Cᵢ` (`t, cᵢ ≥ 0`, `Cᵢ` left-supported), the exponential `exp D` is a
reflection-positive trace weight. -/
theorem rpInteractionExp_reflectionPositive {ι : Type} [Fintype ι]
    (C : ι → ManyBodyOpS (Fin (2 * n)) N) (hC : ∀ i, SupportedOnLeftS n N (C i))
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) {t : ℝ} (ht : 0 ≤ t) :
    RPTraceWeightS n N
      (NormedSpace.exp ((t : ℂ) • ∑ i, (c i : ℂ) • (ringReflectionThetaS n N (C i) * C i))) := by
  haveI : CompleteSpace (ManyBodyOpS (Fin (2 * n)) N) :=
    FiniteDimensional.complete ℂ (ManyBodyOpS (Fin (2 * n)) N)
  set D := (t : ℂ) • ∑ i, (c i : ℂ) • (ringReflectionThetaS n N (C i) * C i) with hDdef
  have hDcone : RPTraceConeRepS n N D :=
    RPTraceConeRepS.smul_nonneg ht ⟨ι, inferInstance, C, c, hC, hc, rfl⟩
  -- every partial sum of the exponential series is cone-representable
  have hcone : ∀ m,
      RPTraceConeRepS n N (∑ k ∈ Finset.range m, ((Nat.factorial k : ℂ))⁻¹ • D ^ k) := by
    intro m
    induction m with
    | zero => simpa using RPTraceConeRepS.zero
    | succ m ih =>
      rw [Finset.sum_range_succ]
      refine ih.add ?_
      rw [show ((Nat.factorial m : ℂ))⁻¹ = (((Nat.factorial m : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring]
      exact (hDcone.pow m).smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  -- the partial sums converge to `exp D`
  have hexp : Filter.Tendsto (fun m => ∑ k ∈ Finset.range m, ((Nat.factorial k : ℂ))⁻¹ • D ^ k)
      Filter.atTop (𝓝 (NormedSpace.exp D)) := by
    rw [congrFun (NormedSpace.exp_eq_tsum ℂ) D]
    exact (NormedSpace.expSeries_summable' (𝕂 := ℂ) D).hasSum.tendsto_sum_nat
  exact RPTraceWeightS.tendsto (fun m => (hcone m).rpTraceWeight) hexp

end LatticeSystem.Quantum
