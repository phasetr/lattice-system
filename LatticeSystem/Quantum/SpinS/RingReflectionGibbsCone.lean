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

/-- The product of two (possibly field-crossing) cone generators is again a cone generator:
`(θ(A)·B)·(θ(A')·B') = θ(A·A')·(B·B')`, using `θ`'s multiplicativity and the left/right commutation
`B·θ(A') = θ(A')·B`.  Only the reflected-adjacent factor `B` and the reflected factor `A'` need be
left-supported (weakest hypotheses); `A`, `B'` are unconstrained.  For the diagonal cone
(`A = B`, `A' = B'`) this specialises to `(θ(C)·C)·(θ(D)·D) = θ(C·D)·(C·D)`; the off-diagonal case
`A = C v ≠ B = C u` closes the field-crossing product of `RPTwoFieldConeRepS.mul`. -/
theorem weightGen_mul {A B A' B' : ManyBodyOpS (Fin (2 * n)) N} (hB : SupportedOnLeftS n N B)
    (hA' : SupportedOnLeftS n N A') :
    (ringReflectionThetaS n N A * B) * (ringReflectionThetaS n N A' * B')
      = ringReflectionThetaS n N (A * A') * (B * B') := by
  rw [ringReflectionThetaS_mul,
    show (ringReflectionThetaS n N A * B) * (ringReflectionThetaS n N A' * B')
        = ringReflectionThetaS n N A * (B * ringReflectionThetaS n N A') * B' by
      simp only [mul_assoc],
    hB.mul_theta_comm hA',
    show ringReflectionThetaS n N A * (ringReflectionThetaS n N A' * B) * B'
        = (ringReflectionThetaS n N A * ringReflectionThetaS n N A') * (B * B') by
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

/-- The exponential partial sums `∑_{k<r} (k!)⁻¹ • Pᵏ` of a cone-representable operator `P` are
cone-representable — the `r → ∞` cone approximants of `exp P` — by closure of `RPTraceConeRepS`
under `one`/`add`/`smul_nonneg`/`pow`.  Extracted so both `RPTraceWeightS.mul_exp_coneRep_right`
and the two-field reflection Cauchy–Schwarz double limit of Tasaki (4.1.51) (pp. 89–93; DLS 1978
§2–3) consume the same induction. -/
theorem RPTraceConeRepS.expSeriesPartialSum {P : ManyBodyOpS (Fin (2 * n)) N}
    (hP : RPTraceConeRepS n N P) (r : ℕ) :
    RPTraceConeRepS n N (∑ k ∈ Finset.range r, ((Nat.factorial k : ℂ))⁻¹ • P ^ k) := by
  induction r with
  | zero => simpa using RPTraceConeRepS.zero
  | succ r ih =>
    rw [Finset.sum_range_succ]
    refine ih.add ?_
    rw [show ((Nat.factorial r : ℂ))⁻¹ = (((Nat.factorial r : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring]
    exact (hP.pow r).smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- A **field-dependent two-field cone representation** of a crossing
`P : (field) → (field) → op`: there is a field-independent finite index family `ι` with
field-independent nonnegative weights `c`, and field-dependent left-supported generators `C i z`,
such that for every field pair `(u, v)`
`P u v = ∑ᵢ cᵢ • (θ(C i v) · C i u)` (the reflected pile carries the field `v`, the non-reflected
pile the field `u`).  The diagonal `u = v` is a genuine `θ(A)·A` cone; the off-diagonal `u ≠ v`
is the field-crossing form.  The field-free `RPTraceConeRepS n N M` embeds as the constant family
`C i z := Ĉ i` (bridge `RPTraceConeRepS.toField`), so this is a true generalisation, not a
duplicate.  It closes under the algebraic operations exactly as `RPTraceConeRepS`, giving the shared
field-crossing cone family that the three slots of the two-field reflection Cauchy–Schwarz of Tasaki
(4.1.51)/(4.1.69) (pp. 89–93; DLS 1978 §2–3) consume. -/
def RPTwoFieldConeRepS (n N : ℕ)
    (P : (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (C : ι → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N)
    (c : ι → ℝ),
    (∀ i z, SupportedOnLeftS n N (C i z)) ∧ (∀ i, 0 ≤ c i)
      ∧ ∀ u v, P u v = ∑ i, (c i : ℂ) • (ringReflectionThetaS n N (C i v) * C i u)

/-- The constant crossing `1` is field-cone-representable (`1 = 1 • (θ(1)·1)` at every field). -/
theorem RPTwoFieldConeRepS.one : RPTwoFieldConeRepS n N (fun _ _ => 1) := by
  refine ⟨PUnit, inferInstance, fun _ _ => 1, fun _ => 1, fun _ _ => SupportedOnLeftS.one,
    fun _ => zero_le_one, ?_⟩
  intro u v
  simp [ringReflectionThetaS_one]

/-- The constant crossing `0` is field-cone-representable (empty / zero-coefficient combination). -/
theorem RPTwoFieldConeRepS.zero : RPTwoFieldConeRepS n N (fun _ _ => 0) := by
  refine ⟨PUnit, inferInstance, fun _ _ => 1, fun _ => 0, fun _ _ => SupportedOnLeftS.one,
    fun _ => le_refl 0, ?_⟩
  intro u v
  simp

/-- Field-cone-representability is closed under pointwise sums (field-independent index disjoint
union `ι ⊕ κ`, generators/weights threaded through the field). -/
theorem RPTwoFieldConeRepS.add
    {P Q : (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N}
    (hP : RPTwoFieldConeRepS n N P) (hQ : RPTwoFieldConeRepS n N Q) :
    RPTwoFieldConeRepS n N (fun u v => P u v + Q u v) := by
  obtain ⟨ι, _, C, c, hC, hc, hPeq⟩ := hP
  obtain ⟨κ, _, D, d, hD, hd, hQeq⟩ := hQ
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim C D, Sum.elim c d, ?_, ?_, ?_⟩
  · rintro (i | j) z
    · exact hC i z
    · exact hD j z
  · rintro (i | j)
    · exact hc i
    · exact hd j
  · intro u v
    simp only [hPeq u v, hQeq u v, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Field-cone-representability is closed under nonnegative scaling (scale the field-independent
weights). -/
theorem RPTwoFieldConeRepS.smul_nonneg
    {P : (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N} {a : ℝ} (ha : 0 ≤ a)
    (hP : RPTwoFieldConeRepS n N P) : RPTwoFieldConeRepS n N (fun u v => (a : ℂ) • P u v) := by
  obtain ⟨ι, _, C, c, hC, hc, hPeq⟩ := hP
  refine ⟨ι, inferInstance, C, fun i => a * c i, hC, fun i => mul_nonneg ha (hc i), ?_⟩
  intro u v
  simp only [hPeq u v, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_smul]
  push_cast
  ring_nf

/-- Field-cone-representability is closed under pointwise products, using the four-operator
`weightGen_mul`: the composed generator is the fieldwise product `(C i · D j) z := C i z · D j z`
(left-supported at every field), and the field-crossing product
`(θ(C i v)·C i u)·(θ(D j v)·D j u) = θ((C i·D j) v)·((C i·D j) u)` closes the sum. -/
theorem RPTwoFieldConeRepS.mul
    {P Q : (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N}
    (hP : RPTwoFieldConeRepS n N P) (hQ : RPTwoFieldConeRepS n N Q) :
    RPTwoFieldConeRepS n N (fun u v => P u v * Q u v) := by
  obtain ⟨ι, _, C, c, hC, hc, hPeq⟩ := hP
  obtain ⟨κ, _, D, d, hD, hd, hQeq⟩ := hQ
  refine ⟨ι × κ, inferInstance, fun p z => C p.1 z * D p.2 z, fun p => c p.1 * d p.2,
    fun p z => (hC p.1 z).mul (hD p.2 z), fun p => mul_nonneg (hc p.1) (hd p.2), ?_⟩
  intro u v
  simp only [hPeq u v, hQeq u v]
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [smul_mul_smul_comm, weightGen_mul (hC p.1 u) (hD p.2 v)]
  push_cast
  ring_nf

/-- Field-cone-representability is closed under (natural) powers (fieldwise, from `mul`). -/
theorem RPTwoFieldConeRepS.pow
    {P : (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N}
    (hP : RPTwoFieldConeRepS n N P) :
    ∀ k : ℕ, RPTwoFieldConeRepS n N (fun u v => (P u v) ^ k)
  | 0 => by simpa using RPTwoFieldConeRepS.one
  | k + 1 => by simpa only [pow_succ] using (RPTwoFieldConeRepS.pow hP k).mul hP

/-- The exponential partial sums `∑_{k<r} (k!)⁻¹ • (P u v)ᵏ` of a field-crossing cone `P` are again
a field-crossing cone (fieldwise, from `one`/`add`/`smul_nonneg`/`pow`) — the `r → ∞` cone
approximants of `exp (P u v)` shared across the three slots of the two-field reflection
Cauchy–Schwarz of Tasaki (4.1.51) (pp. 89–93; DLS 1978 §2–3). -/
theorem RPTwoFieldConeRepS.expSeriesPartialSum
    {P : (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N}
    (hP : RPTwoFieldConeRepS n N P) (r : ℕ) :
    RPTwoFieldConeRepS n N
      (fun u v => ∑ k ∈ Finset.range r, ((Nat.factorial k : ℂ))⁻¹ • (P u v) ^ k) := by
  induction r with
  | zero => simpa using RPTwoFieldConeRepS.zero
  | succ r ih =>
    simp only [Finset.sum_range_succ]
    refine ih.add ?_
    rw [show ((Nat.factorial r : ℂ))⁻¹ = (((Nat.factorial r : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring]
    exact (hP.pow r).smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- **Field-free bridge.**  A (field-independent) cone-representable weight `M` lifts to the
constant field-crossing cone `fun _ _ => M` via the constant generator family `C i z := Ĉ i`.
This is a plain coercion (not a duplicate declaration): it recovers `RPTraceConeRepS` as the
`u = v`, constant-in-field degenerate case of `RPTwoFieldConeRepS`. -/
theorem RPTraceConeRepS.toField {M : ManyBodyOpS (Fin (2 * n)) N}
    (hM : RPTraceConeRepS n N M) : RPTwoFieldConeRepS n N (fun _ _ => M) := by
  obtain ⟨ι, _, C, c, hC, hc, rfl⟩ := hM
  exact ⟨ι, inferInstance, fun i _ => C i, c, fun i _ => hC i, hc, fun _ _ => rfl⟩

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
