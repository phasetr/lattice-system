/-
The reflection-positive trace-weight cone and its closure properties
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 6).

A **reflection-positive trace weight** is an operator `M` for which `X ↦ Tr(M · X)` is a
reflection-positive functional (`RPTraceWeightS`).  The weighted trace cone
(`RingReflectionWeightedCone`)
shows that every nonnegative finite combination `∑ cᵢ θ(Cᵢ)·Cᵢ` of left-supported weights is such an
`M`; here we package those combinations as the predicate `RPTraceConeRepS`, prove it is closed under
the algebraic operations (`one`/`add`/`smul`/`mul`/`pow`), show every representable weight is an
RP trace weight, and that RP trace weights are closed under limits (finite-dimensional trace
continuity).  These are the cone on which the next layer mounts the interaction-part Gibbs
exponential `exp (t · ∑ cᵢ θ(Cᵢ)·Cᵢ)` (a limit of cone-representable partial sums) for the
Dyson–Lieb–Simon / Shastry argument.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionWeightedCone
import Mathlib.Topology.Instances.Matrix

namespace LatticeSystem.Quantum

open Matrix Filter Topology

variable {n N : ℕ}

/-- An operator `M` is a **reflection-positive trace weight** when the functional `X ↦ Tr(M · X)` is
reflection positive, i.e. `0 ≤ Re Tr(M · (θ(A)·A))` for every left-supported `A`. -/
def RPTraceWeightS (n N : ℕ) (M : ManyBodyOpS (Fin (2 * n)) N) : Prop :=
  ReflectionPositiveFunctionalS n N (fun X => (M * X).trace)

/-- The product of two cone generators is again a cone generator:
`(θ(C)·C)·(θ(D)·D) = θ(C·D)·(C·D)`, using `θ`'s multiplicativity and the left/right commutation. -/
theorem weightGen_mul {C D : ManyBodyOpS (Fin (2 * n)) N} (hC : SupportedOnLeftS n N C)
    (hD : SupportedOnLeftS n N D) :
    (ringReflectionThetaS n N C * C) * (ringReflectionThetaS n N D * D)
      = ringReflectionThetaS n N (C * D) * (C * D) := by
  rw [ringReflectionThetaS_mul,
    show (ringReflectionThetaS n N C * C) * (ringReflectionThetaS n N D * D)
        = ringReflectionThetaS n N C * (C * ringReflectionThetaS n N D) * D by
      simp only [mul_assoc],
    hC.mul_theta_comm hD,
    show ringReflectionThetaS n N C * (ringReflectionThetaS n N D * C) * D
        = (ringReflectionThetaS n N C * ringReflectionThetaS n N D) * (C * D) by
      simp only [mul_assoc]]

/-- `M` is **cone-representable** when it is a nonnegative finite combination
`∑ᵢ cᵢ • (θ(Cᵢ)·Cᵢ)` of left-supported weights. -/
def RPTraceConeRepS (n N : ℕ) (M : ManyBodyOpS (Fin (2 * n)) N) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (C : ι → ManyBodyOpS (Fin (2 * n)) N) (c : ι → ℝ),
    (∀ i, SupportedOnLeftS n N (C i)) ∧ (∀ i, 0 ≤ c i)
      ∧ M = ∑ i, (c i : ℂ) • (ringReflectionThetaS n N (C i) * C i)

/-- The identity is cone-representable (`1 = 1 • (θ(1)·1)`). -/
theorem RPTraceConeRepS.one : RPTraceConeRepS n N 1 := by
  refine ⟨PUnit, inferInstance, fun _ => 1, fun _ => 1, fun _ => SupportedOnLeftS.one,
    fun _ => zero_le_one, ?_⟩
  simp [ringReflectionThetaS_one]

/-- The zero operator is cone-representable (empty / zero-coefficient combination). -/
theorem RPTraceConeRepS.zero : RPTraceConeRepS n N 0 :=
  ⟨PUnit, inferInstance, fun _ => 1, fun _ => 0, fun _ => SupportedOnLeftS.one,
    fun _ => le_refl 0, by simp⟩

/-- Cone-representability is closed under sums. -/
theorem RPTraceConeRepS.add {M M' : ManyBodyOpS (Fin (2 * n)) N}
    (hM : RPTraceConeRepS n N M) (hM' : RPTraceConeRepS n N M') :
    RPTraceConeRepS n N (M + M') := by
  obtain ⟨ι, _, C, c, hC, hc, rfl⟩ := hM
  obtain ⟨κ, _, D, d, hD, hd, rfl⟩ := hM'
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim C D, Sum.elim c d, ?_, ?_, ?_⟩
  · rintro (i | j) <;> simp [hC, hD]
  · rintro (i | j) <;> simp [hc, hd]
  · rw [Fintype.sum_sum_type]; simp

/-- Cone-representability is closed under nonnegative scaling. -/
theorem RPTraceConeRepS.smul_nonneg {M : ManyBodyOpS (Fin (2 * n)) N} {a : ℝ} (ha : 0 ≤ a)
    (hM : RPTraceConeRepS n N M) : RPTraceConeRepS n N ((a : ℂ) • M) := by
  obtain ⟨ι, _, C, c, hC, hc, rfl⟩ := hM
  refine ⟨ι, inferInstance, C, fun i => a * c i, hC, fun i => mul_nonneg ha (hc i), ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_smul]
  push_cast
  ring_nf

/-- Cone-representability is closed under products (using `weightGen_mul`). -/
theorem RPTraceConeRepS.mul {M M' : ManyBodyOpS (Fin (2 * n)) N}
    (hM : RPTraceConeRepS n N M) (hM' : RPTraceConeRepS n N M') :
    RPTraceConeRepS n N (M * M') := by
  obtain ⟨ι, _, C, c, hC, hc, rfl⟩ := hM
  obtain ⟨κ, _, D, d, hD, hd, rfl⟩ := hM'
  refine ⟨ι × κ, inferInstance, fun p => C p.1 * D p.2, fun p => c p.1 * d p.2,
    fun p => (hC p.1).mul (hD p.2), fun p => mul_nonneg (hc p.1) (hd p.2), ?_⟩
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [smul_mul_smul_comm, weightGen_mul (hC p.1) (hD p.2)]
  push_cast
  ring_nf

/-- Cone-representability is closed under (natural) powers. -/
theorem RPTraceConeRepS.pow {M : ManyBodyOpS (Fin (2 * n)) N} (hM : RPTraceConeRepS n N M) :
    ∀ k : ℕ, RPTraceConeRepS n N (M ^ k)
  | 0 => by simpa using RPTraceConeRepS.one
  | k + 1 => by rw [pow_succ]; exact (RPTraceConeRepS.pow hM k).mul hM

/-- A cone-representable weight is a reflection-positive trace weight. -/
theorem RPTraceConeRepS.rpTraceWeight {M : ManyBodyOpS (Fin (2 * n)) N}
    (hM : RPTraceConeRepS n N M) : RPTraceWeightS n N M := by
  obtain ⟨ι, _, C, c, hC, hc, rfl⟩ := hM
  intro A hA
  have := weightedTraceFunctional_reflectionPositive_finsetSum (n := n) (N := N) Finset.univ C
    (fun i _ => hC i) c (fun i _ => hc i) A hA
  simpa only [Finset.sum_mul] using this

/-- Reflection-positive trace weights are closed under limits: if `Mₖ → M` and every `Mₖ` is an RP
trace weight, then so is `M` (finite-dimensional trace continuity). -/
theorem RPTraceWeightS.tendsto {Mseq : ℕ → ManyBodyOpS (Fin (2 * n)) N}
    {M : ManyBodyOpS (Fin (2 * n)) N} (hseq : ∀ k, RPTraceWeightS n N (Mseq k))
    (hlim : Filter.Tendsto Mseq Filter.atTop (𝓝 M)) : RPTraceWeightS n N M := by
  intro A hA
  have hcont : Continuous (fun M' : ManyBodyOpS (Fin (2 * n)) N =>
      (M' * (ringReflectionThetaS n N A * A)).trace.re) :=
    Complex.continuous_re.comp
      (Continuous.matrix_trace (continuous_id.mul continuous_const))
  have htend := (hcont.tendsto M).comp hlim
  exact ge_of_tendsto' htend (fun k => hseq k A hA)

end LatticeSystem.Quantum
