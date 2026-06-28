/-
The matrix exponential preserves the left-half subalgebra and commutes with the reflection map
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 8).

Two building blocks for the Hamiltonian factor `e^{-βH_L}` of the full Gibbs reflection-positivity
decomposition:

* `SupportedOnLeftS.exp` — if `X` is left-supported then so is `exp X` (the left-half subalgebra is
  a closed subalgebra: it is closed under products, sums, scalars, and entrywise limits, and `exp X`
  is the limit of its partial sums).
* `ringReflectionThetaS_exp` — `θ (exp X) = exp (θ X)`: the reflection map (a continuous
  conjugate-linear `*`-automorphism with real exponential coefficients) commutes with `exp`.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionGibbsExp

namespace LatticeSystem.Quantum

open Matrix Filter Topology

open scoped Matrix.Norms.Operator

variable {n N : ℕ}

/-- The left-half subalgebra is closed under natural powers. -/
theorem SupportedOnLeftS.pow {A : ManyBodyOpS (Fin (2 * n)) N} (hA : SupportedOnLeftS n N A) :
    ∀ k : ℕ, SupportedOnLeftS n N (A ^ k)
  | 0 => by simpa using SupportedOnLeftS.one
  | k + 1 => by rw [pow_succ]; exact (SupportedOnLeftS.pow hA k).mul hA

/-- Left-supportedness is closed under entrywise limits: if `Mₖ → M` and every `Mₖ` is
left-supported, then so is `M` (both support conditions are closed conditions on the matrix
entries). -/
theorem SupportedOnLeftS.of_tendsto {Mseq : ℕ → ManyBodyOpS (Fin (2 * n)) N}
    {M : ManyBodyOpS (Fin (2 * n)) N} (h : ∀ k, SupportedOnLeftS n N (Mseq k))
    (hlim : Filter.Tendsto Mseq Filter.atTop (𝓝 M)) : SupportedOnLeftS n N M := by
  refine ⟨fun σ τ hne i hi => ?_, fun σ τ σ' τ' h1 h2 h3 h4 => ?_⟩
  · by_contra hcon
    have hz : ∀ k, Mseq k σ τ = 0 := fun k => by
      by_contra hk; exact hcon ((h k).1 σ τ hk i hi)
    have hlim2 : Filter.Tendsto (fun k => Mseq k σ τ) Filter.atTop (𝓝 (M σ τ)) :=
      ((continuous_apply_apply σ τ).tendsto M).comp hlim
    simp only [hz] at hlim2
    exact hne (tendsto_nhds_unique tendsto_const_nhds hlim2).symm
  · have e1 : Filter.Tendsto (fun k => Mseq k σ τ) Filter.atTop (𝓝 (M σ τ)) :=
      ((continuous_apply_apply σ τ).tendsto M).comp hlim
    have e2 : Filter.Tendsto (fun k => Mseq k σ' τ') Filter.atTop (𝓝 (M σ' τ')) :=
      ((continuous_apply_apply σ' τ').tendsto M).comp hlim
    have heq : (fun k => Mseq k σ τ) = fun k => Mseq k σ' τ' :=
      funext fun k => (h k).2 σ τ σ' τ' h1 h2 h3 h4
    rw [heq] at e1
    exact tendsto_nhds_unique e1 e2

/-- **The exponential preserves left-supportedness.**  If `X` is left-supported then `exp X` is. -/
theorem SupportedOnLeftS.exp {X : ManyBodyOpS (Fin (2 * n)) N} (hX : SupportedOnLeftS n N X) :
    SupportedOnLeftS n N (NormedSpace.exp X) := by
  haveI : CompleteSpace (ManyBodyOpS (Fin (2 * n)) N) :=
    FiniteDimensional.complete ℂ (ManyBodyOpS (Fin (2 * n)) N)
  refine SupportedOnLeftS.of_tendsto
    (Mseq := fun m => ∑ k ∈ Finset.range m, ((Nat.factorial k : ℂ))⁻¹ • X ^ k) ?_ ?_
  · intro m
    induction m with
    | zero => simpa using SupportedOnLeftS.zero
    | succ m ih =>
      simp only [Finset.sum_range_succ]
      exact ih.add ((hX.pow m).smul _)
  · rw [congrFun (NormedSpace.exp_eq_tsum ℂ) X]
    exact (NormedSpace.expSeries_summable' (𝕂 := ℂ) X).hasSum.tendsto_sum_nat

/-- `θ` is compatible with natural powers: `θ (X ^ k) = (θ X) ^ k`. -/
theorem ringReflectionThetaS_pow (X : ManyBodyOpS (Fin (2 * n)) N) (k : ℕ) :
    ringReflectionThetaS n N (X ^ k) = (ringReflectionThetaS n N X) ^ k := by
  induction k with
  | zero => simp [ringReflectionThetaS_one]
  | succ k ih => rw [pow_succ, pow_succ, ringReflectionThetaS_mul, ih]

/-- The reflection map `θ` is continuous (it conjugates and reindexes the matrix entries). -/
theorem ringReflectionThetaS_continuous :
    Continuous (ringReflectionThetaS n N) := by
  refine continuous_matrix (fun σ τ => ?_)
  simp only [ringReflectionThetaS_apply]
  exact RCLike.continuous_conj.comp (continuous_apply_apply _ _)

/-- **`θ` commutes with the exponential.**  `θ (exp X) = exp (θ X)`. -/
theorem ringReflectionThetaS_exp (X : ManyBodyOpS (Fin (2 * n)) N) :
    ringReflectionThetaS n N (NormedSpace.exp X)
      = NormedSpace.exp (ringReflectionThetaS n N X) := by
  haveI : CompleteSpace (ManyBodyOpS (Fin (2 * n)) N) :=
    FiniteDimensional.complete ℂ (ManyBodyOpS (Fin (2 * n)) N)
  -- `θ` applied to the `m`-th partial sum equals the `m`-th partial sum for `θ X`
  have hθP : ∀ m, ringReflectionThetaS n N (∑ k ∈ Finset.range m, ((Nat.factorial k : ℂ))⁻¹ • X ^ k)
      = ∑ k ∈ Finset.range m, ((Nat.factorial k : ℂ))⁻¹ • (ringReflectionThetaS n N X) ^ k := by
    intro m
    induction m with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      ext σ τ; simp [ringReflectionThetaS_apply]
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ringReflectionThetaS_add, ih,
        ringReflectionThetaS_smul, ringReflectionThetaS_pow]
      congr 2
      simp [map_inv₀]
  have hX : Filter.Tendsto
      (fun m => ∑ k ∈ Finset.range m, ((Nat.factorial k : ℂ))⁻¹ • X ^ k)
      Filter.atTop (𝓝 (NormedSpace.exp X)) := by
    rw [congrFun (NormedSpace.exp_eq_tsum ℂ) X]
    exact (NormedSpace.expSeries_summable' (𝕂 := ℂ) X).hasSum.tendsto_sum_nat
  have hθX : Filter.Tendsto
      (fun m => ∑ k ∈ Finset.range m, ((Nat.factorial k : ℂ))⁻¹ • (ringReflectionThetaS n N X) ^ k)
      Filter.atTop (𝓝 (NormedSpace.exp (ringReflectionThetaS n N X))) := by
    rw [congrFun (NormedSpace.exp_eq_tsum ℂ) (ringReflectionThetaS n N X)]
    exact (NormedSpace.expSeries_summable' (𝕂 := ℂ)
      (ringReflectionThetaS n N X)).hasSum.tendsto_sum_nat
  have h1 := (ringReflectionThetaS_continuous.tendsto (NormedSpace.exp X)).comp hX
  simp only [Function.comp_def, hθP] at h1
  exact tendsto_nhds_unique h1 hθX

end LatticeSystem.Quantum
