/-
The two-field product pairing identity — the SWEEP step of the doubled Cauchy–Schwarz
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer: Gaussian domination PR7b-iii-a, p. 86).

The doubled Dyson–Lieb–Simon approximant `(G(x)·θ(G(y))·E^{(r)})^m` carries two independent fields
`x`, `y`: a left kinetic factor `G(x)` (left-supported), its reflected partner `θ(G(y))`, and the
crossing factor expanded into its nonnegative cone form `E^{(r)} = ∑ᵢ wᵢ·(θ(Cᵢ)·Cᵢ)` with `wᵢ ≥ 0`
and `Cᵢ` left-supported.  This file proves that sweeping every left-supported factor to the
right and every reflected `θ(·)` factor to the left collapses the `m`-fold product into a
single reflection
pairing

    `(G(x)·θ(G(y))·∑ᵢ wᵢ·(θ(Cᵢ)·Cᵢ))^m = ∑_ȷ⃗ v_ȷ⃗ · (θ(𝓛_ȷ⃗(y)) · 𝓛_ȷ⃗(x))`,

over the crossing-index family `κ = ιᵐ`, where `v_ȷ⃗ = ∏ w ≥ 0` and the pattern-shared family
`𝓛_ȷ⃗(z) = G(z)·C_{i₁}·…·G(z)·C_{iₘ}` (left-supported, depending on the field only through `z`, with
the SAME crossing sequence `ȷ⃗` in both piles).  The one algebraic ingredient in each induction step
is the disjoint-support commutation `SupportedOnLeftS.mul_theta_comm` (a left-supported operator
commutes with `θ` of a left-supported operator), together with the multiplicativity of `θ`.

Taking the trace of the pairing and applying the bilinear reflection base identity
`trace_theta_mul_eq_refLeftSum_mul` termwise gives the weighted ℓ² Gram form (†)

    `Tr(U) = ∑_ȷ⃗ v_ȷ⃗ · conj(refLeftSum 𝓛_ȷ⃗(y)) · refLeftSum 𝓛_ȷ⃗(x)`,

on which the doubled reflection Cauchy–Schwarz (PR7b-iii-b/c) mounts the abstract Gram inequality.
This file proves only the operator SWEEP identity (`twoField_product_pairing`) and its trace
corollary (`twoField_product_pairing_trace`); the Cauchy–Schwarz inequality and the double limit are
deferred to the next PRs of the arc.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionWeightedCone

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **SWEEP operator identity, single step.**  For left-supported `La`, `Ga`, `Gb`, `Cb` the mixed
product formed by appending one doubled-kinetic-plus-crossing factor rearranges into a single
reflection pairing.  The two piles now carry DIFFERENT crossing generators — the reflected pile the
`y`-field factor `Cb` (`= C i y`), the non-reflected pile the `x`-field factor `Ca` (`= C i x`) —
the field entering both the kinetic factors `La`/`Ga`, `Lb`/`Gb` and the crossing factors `Ca`/`Cb`:

    `θ(Lb)·La · (Ga·θ(Gb)·(θ(Cb)·Ca)) = θ(Lb·Gb·Cb) · (La·Ga·Ca)`.

The proof moves the left-supported block `La·Ga` to the right past the reflected block
`θ(Gb)·θ(Cb) = θ(Gb·Cb)` by the disjoint-support commutation `SupportedOnLeftS.mul_theta_comm`; the
remaining reassociations are pure monoid bookkeeping.  The trailing non-reflected crossing `Ca`
stays to the far right and never crosses `θ`, so — like the reflected header `Lb` — it needs no
support hypothesis. -/
private theorem sweep_operator_identity {La Lb Ga Gb Ca Cb : ManyBodyOpS (Fin (2 * n)) N}
    (hLa : SupportedOnLeftS n N La) (hGa : SupportedOnLeftS n N Ga)
    (hGb : SupportedOnLeftS n N Gb) (hCb : SupportedOnLeftS n N Cb) :
    ringReflectionThetaS n N Lb * La
        * (Ga * ringReflectionThetaS n N Gb * (ringReflectionThetaS n N Cb * Ca))
      = ringReflectionThetaS n N (Lb * Gb * Cb) * (La * Ga * Ca) := by
  have hcomm : La * Ga * (ringReflectionThetaS n N Gb * ringReflectionThetaS n N Cb)
      = ringReflectionThetaS n N Gb * ringReflectionThetaS n N Cb * (La * Ga) := by
    have h := (hLa.mul hGa).mul_theta_comm (hGb.mul hCb)
    rwa [ringReflectionThetaS_mul] at h
  rw [ringReflectionThetaS_mul, ringReflectionThetaS_mul]
  calc ringReflectionThetaS n N Lb * La
          * (Ga * ringReflectionThetaS n N Gb * (ringReflectionThetaS n N Cb * Ca))
      = ringReflectionThetaS n N Lb
          * (La * Ga * (ringReflectionThetaS n N Gb * ringReflectionThetaS n N Cb)) * Ca := by
        noncomm_ring
    _ = ringReflectionThetaS n N Lb
          * (ringReflectionThetaS n N Gb * ringReflectionThetaS n N Cb * (La * Ga)) * Ca := by
        rw [hcomm]
    _ = ringReflectionThetaS n N Lb * ringReflectionThetaS n N Gb * ringReflectionThetaS n N Cb
          * (La * Ga * Ca) := by noncomm_ring

/-- **Two-field product pairing (the SWEEP identity).**  The doubled Dyson–Lieb–Simon approximant
`(g(x)·θ(g(y))·∑ᵢ wᵢ·(θ(Cᵢ(y))·Cᵢ(x)))^m` — with left-supported kinetic family `g`, nonnegative cone
weights `wᵢ ≥ 0`, and a FIELD-DEPENDENT left-supported crossing family `Cᵢ(z)` (the reflected pile
carrying the `y`-field factor `Cᵢ(y)`, the non-reflected pile the `x`-field factor `Cᵢ(x)`) —
collapses into a single nonnegative reflection pairing over the crossing family `κ = ιᵐ`:

    `(g(x)·θ(g(y))·∑ᵢ wᵢ·(θ(Cᵢ(y))·Cᵢ(x)))^m = ∑ₖ vₖ·(θ(𝓛ₖ(y)) · 𝓛ₖ(x))`,

where `vₖ = ∏ w ≥ 0` and the pattern-shared family `𝓛ₖ(z) = g(z)·C_{i₁}(z)·…·g(z)·C_{iₘ}(z)` is
left-supported, with the SAME crossing sequence `k` in both piles and the field entering through
`z`.  Proved by induction on `m`, each step appending one factor and sweeping the appended
left-supported block past the reflected block via `sweep_operator_identity`.  The field-free pairing
is the constant specialization `C i z := C i`. -/
theorem twoField_product_pairing (m : ℕ)
    (g : (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N)
    (hg : ∀ x, SupportedOnLeftS n N (g x)) {ι : Type} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (C : ι → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N)
    (hC : ∀ i z, SupportedOnLeftS n N (C i z)) :
    ∃ (κ : Type) (_ : Fintype κ) (v : κ → ℝ)
      (𝓛 : κ → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N),
      (∀ k, 0 ≤ v k) ∧ (∀ k x, SupportedOnLeftS n N (𝓛 k x)) ∧
        ∀ x y, (g x * ringReflectionThetaS n N (g y)
              * ∑ i, (w i : ℂ) • (ringReflectionThetaS n N (C i y) * C i x)) ^ m
          = ∑ k, (v k : ℂ) • (ringReflectionThetaS n N (𝓛 k y) * 𝓛 k x) := by
  induction m with
  | zero =>
    refine ⟨PUnit, inferInstance, fun _ => 1, fun _ _ => 1, fun _ => zero_le_one,
      fun _ _ => SupportedOnLeftS.one, ?_⟩
    intro x y
    simp [ringReflectionThetaS_one]
  | succ m ih =>
    obtain ⟨κ, instκ, v, 𝓛, hv, hsupp, heq⟩ := ih
    refine ⟨κ × ι, inferInstance, fun p => v p.1 * w p.2,
      fun p z => 𝓛 p.1 z * g z * C p.2 z, fun p => mul_nonneg (hv p.1) (hw p.2),
      fun p z => ((hsupp p.1 z).mul (hg z)).mul (hC p.2 z), ?_⟩
    intro x y
    rw [pow_succ, heq x y, Finset.sum_mul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_mul_assoc, mul_smul_comm, mul_smul_comm, smul_smul,
      sweep_operator_identity (hsupp k x) (hg x) (hg y) (hC i y), Complex.ofReal_mul]

/-- **The pairing trace form (†).**  Taking the trace of the SWEEP identity
`twoField_product_pairing` and applying the bilinear reflection base identity
`trace_theta_mul_eq_refLeftSum_mul` to each pairing term yields the weighted ℓ² Gram form

    `Tr(U) = ∑ₖ vₖ · conj(refLeftSum 𝓛ₖ(y)) · refLeftSum 𝓛ₖ(x)`,

with `vₖ ≥ 0` and the same left-supported pattern-shared family `𝓛ₖ`.  This is the finite Gram
pairing consumed by the doubled reflection Cauchy–Schwarz (PR7b-iii-b). -/
theorem twoField_product_pairing_trace (m : ℕ)
    (g : (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N)
    (hg : ∀ x, SupportedOnLeftS n N (g x)) {ι : Type} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (C : ι → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N)
    (hC : ∀ i z, SupportedOnLeftS n N (C i z)) :
    ∃ (κ : Type) (_ : Fintype κ) (v : κ → ℝ)
      (𝓛 : κ → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N),
      (∀ k, 0 ≤ v k) ∧ (∀ k x, SupportedOnLeftS n N (𝓛 k x)) ∧
        ∀ x y, ((g x * ringReflectionThetaS n N (g y)
              * ∑ i, (w i : ℂ) • (ringReflectionThetaS n N (C i y) * C i x)) ^ m).trace
          = ∑ k, (v k : ℂ)
              * (starRingEnd ℂ (refLeftSum n N (𝓛 k y)) * refLeftSum n N (𝓛 k x)) := by
  obtain ⟨κ, instκ, v, 𝓛, hv, hsupp, heq⟩ :=
    twoField_product_pairing m g hg w hw C hC
  refine ⟨κ, instκ, v, 𝓛, hv, hsupp, ?_⟩
  intro x y
  rw [heq x y, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.trace_smul, smul_eq_mul,
    trace_theta_mul_eq_refLeftSum_mul (hsupp k y) (hsupp k x)]

end LatticeSystem.Quantum
