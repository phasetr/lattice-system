import LatticeSystem.Quantum.SpinS.MPSTheorem75Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Linear transfer-power substrate for Tasaki Theorem 7.5

This file contains the theorem-specific linear substrate used by the two directions of the
corrected Tasaki Theorem 7.5. It exposes only the concrete finite Kraus transfer, its uniform power
bound, and its faithful weighted-trace power limit. The generic spectral and rank-one arguments
remain private.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.2, Theorem 7.5, eqs. (7.2.41)–(7.2.42), pp. 202–203.
-/

namespace LatticeSystem.Quantum.MPSTheorem75.Internal

open Filter Module
open scoped CStarAlgebra ComplexOrder Topology

variable {D : ℕ}

/-- The concrete finite Kraus transfer `X ↦ Σσ Aσ X Aσᴴ`.

This theorem-specific endpoint is consumed by `MPSTheorem75Choi`,
`MPSTheorem75Peripheral`, and the unit reverse adapter
`mpsSpansForAllLarge_of_unit_faithful_primitive` in `MPSTheorem75`. -/
noncomputable def finiteKrausMap {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ) :
    Module.End ℂ (CStarMatrix (Fin D) (Fin D) ℂ) where
  toFun X := ∑ σ, A σ * X * star (A σ)
  map_add' X Y := by
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp_rw [CStarMatrix.mul_smul, CStarMatrix.smul_mul, Finset.smul_sum]
    simp only [RingHom.id_apply]

/-! ## Positive-unital power bound -/

/-- The concrete finite Kraus transfer bundled as a positive linear map. -/
private noncomputable def finiteKrausPositiveMap {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ) :
    CStarMatrix (Fin D) (Fin D) ℂ →ₚ[ℂ]
      CStarMatrix (Fin D) (Fin D) ℂ :=
  PositiveLinearMap.mk₀ (finiteKrausMap A) fun X hX => by
    change 0 ≤ ∑ σ, A σ * X * star (A σ)
    exact Finset.sum_nonneg fun σ _ => star_right_conjugate_nonneg hX (A σ)

/-- The `n`th iterate of a positive linear map, retained as a positive map. -/
private noncomputable def positivePower
    {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : B →ₚ[ℂ] B) (n : ℕ) : B →ₚ[ℂ] B :=
  PositiveLinearMap.mk₀ (f.toLinearMap ^ n) fun x hx => by
    induction n generalizing x with
    | zero => simpa using hx
    | succ n ih =>
        rw [pow_succ, Module.End.mul_apply]
        exact ih (f x) (f.map_nonneg hx)

/-- A unital positive map has unital positive iterates. -/
private theorem positivePower_apply_one
    {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (f : B →ₚ[ℂ] B) (hf_one : f 1 = 1) (n : ℕ) :
    positivePower f n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (f.toLinearMap ^ (n + 1)) 1 = 1
      change (f.toLinearMap ^ n) 1 = 1 at ih
      have hf_one' : f.toLinearMap 1 = 1 := hf_one
      rw [pow_succ, Module.End.mul_apply, hf_one', ih]

/-- Every power of a positive unital map is bounded by four times the input norm. -/
private theorem norm_positivePower_le
    {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial B]
    (f : B →ₚ[ℂ] B) (hf_one : f 1 = 1) (n : ℕ) (x : B) :
    ‖positivePower f n x‖ ≤ 4 * ‖x‖ := by
  obtain ⟨y, hy_nonneg, hy_norm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg x
  conv_lhs => rw [hy, map_sum]
  simp only [map_smul]
  apply (norm_sum_le _ _).trans
  calc
    (∑ i : Fin 4, ‖(Complex.I ^ (i : ℕ)) • positivePower f n (y i)‖) ≤
        ∑ _i : Fin 4, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa [norm_smul] using
        (PositiveLinearMap.norm_apply_le_of_nonneg (positivePower f n) (y i)
          (hy_nonneg i) |>.trans (by
            rw [positivePower_apply_one f hf_one n, norm_one, one_mul]
            exact hy_norm i))
    _ = 4 * ‖x‖ := by simp

/-- Powers of a positive unital finite Kraus transfer are uniformly bounded by four.

This theorem-specific endpoint is consumed by `MPSTheorem75Peripheral` to bound the transfer
spectrum by the closed unit disk and by `MPSTheorem76Unitary` to force equality of the two
positive normalization constants. -/
theorem norm_finiteKrausMap_pow_le [NeZero D]
    {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (hunital : finiteKrausMap A 1 = 1) (n : ℕ)
    (X : CStarMatrix (Fin D) (Fin D) ℂ) :
    ‖(finiteKrausMap A ^ n) X‖ ≤ 4 * ‖X‖ := by
  let Φ := finiteKrausPositiveMap A
  have hΦone : Φ 1 = 1 := hunital
  simpa only [Φ, finiteKrausPositiveMap, PositiveLinearMap.mk₀] using
    norm_positivePower_le Φ hΦone n X

/-! ## Non-Hermitian rank-one power convergence -/

/-- Spectral radius below one produces a strictly contractive positive power. -/
private theorem exists_pow_norm_lt_one_of_spectralRadius_lt_one
    {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] (a : B)
    (ha : spectralRadius ℂ a < 1) :
    ∃ N : ℕ, 0 < N ∧ ‖a ^ N‖ < 1 := by
  have hroot := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
  have hevent :
      ∀ᶠ N : ℕ in atTop,
        (‖a ^ N‖₊ : ENNReal) ^ (1 / (N : ℝ)) < 1 :=
    (tendsto_order.1 hroot).2 _ ha
  obtain ⟨N, hNroot, hNpos⟩ :=
    (hevent.and (eventually_atTop.2 ⟨1, fun n hn => hn⟩)).exists
  refine ⟨N, hNpos, ?_⟩
  by_contra hN
  have hone : (1 : ENNReal) ≤ ‖a ^ N‖₊ := by
    exact_mod_cast (not_lt.mp hN)
  have hrpow := ENNReal.rpow_le_rpow hone (by positivity : 0 ≤ (1 / (N : ℝ)))
  rw [ENNReal.one_rpow] at hrpow
  exact (not_le_of_gt hNroot) hrpow

/-- A strictly contractive power makes all powers converge to zero. -/
private theorem tendsto_pow_zero_of_exists_pow_norm_lt_one
    {B : Type*} [NormedRing B] [NormOneClass B] (a : B)
    (hcontract : ∃ N : ℕ, 0 < N ∧ ‖a ^ N‖ < 1) :
    Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) := by
  obtain ⟨N, hNpos, hN⟩ := hcontract
  have hdiv : Tendsto (fun n : ℕ => n / N) atTop atTop :=
    Nat.tendsto_div_const_atTop hNpos.ne'
  have hgeom :
      Tendsto (fun n : ℕ => ‖a ^ N‖ ^ (n / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hN).comp hdiv
  let K : ℝ := max 1 ‖a‖ ^ N
  apply squeeze_zero_norm (a := fun n => ‖a ^ N‖ ^ (n / N) * K)
  · intro n
    have hdecomp : a ^ n = (a ^ N) ^ (n / N) * a ^ (n % N) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      exact (Nat.div_add_mod n N).symm
    rw [hdecomp]
    calc
      ‖(a ^ N) ^ (n / N) * a ^ (n % N)‖ ≤
          ‖a ^ N‖ ^ (n / N) * ‖a‖ ^ (n % N) := by
        exact (norm_mul_le ((a ^ N) ^ (n / N)) (a ^ (n % N))).trans <|
          mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ ‖a ^ N‖ ^ (n / N) * K := by
        gcongr
        calc
          ‖a‖ ^ (n % N) ≤ max 1 ‖a‖ ^ (n % N) :=
            pow_le_pow_left₀ (norm_nonneg a) (le_max_right 1 ‖a‖) _
          _ ≤ max 1 ‖a‖ ^ N :=
            pow_le_pow_right₀ (le_max_left 1 ‖a‖)
              (Nat.le_of_lt (Nat.mod_lt n hNpos))
          _ = K := rfl
  · simpa using hgeom.mul_const K

/-- In a complex Banach algebra, spectral radius below one makes powers tend to zero. -/
private theorem tendsto_pow_zero_of_spectralRadius_lt_one
    {B : Type*} [NormedRing B] [NormOneClass B] [NormedAlgebra ℂ B] [CompleteSpace B]
    (a : B) (ha : spectralRadius ℂ a < 1) :
    Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) :=
  tendsto_pow_zero_of_exists_pow_norm_lt_one a
    (exists_pow_norm_lt_one_of_spectralRadius_lt_one a ha)

/-- The rank-one map `x ↦ φ(x) • v`. -/
private def rankOneEnd {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (φ : V →ₗ[ℂ] ℂ) (v : V) : Module.End ℂ V :=
  φ.smulRight v

/-- A normalized functional makes its rank-one map idempotent. -/
private theorem rankOneEnd_sq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (φ : V →ₗ[ℂ] ℂ) (v : V) (hφv : φ v = 1) :
    rankOneEnd φ v ^ 2 = rankOneEnd φ v := by
  ext x
  simp [rankOneEnd, pow_two, Module.End.mul_apply, hφv]

/-- A right fixed vector makes the transfer absorb its rank-one projection on the left. -/
private theorem mul_rankOneEnd
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : Module.End ℂ V) (φ : V →ₗ[ℂ] ℂ) (v : V) (hfv : f v = v) :
    f * rankOneEnd φ v = rankOneEnd φ v := by
  ext x
  simp [rankOneEnd, Module.End.mul_apply, hfv]

/-- A left invariant functional makes its projection absorb the transfer on the right. -/
private theorem rankOneEnd_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : Module.End ℂ V) (φ : V →ₗ[ℂ] ℂ) (v : V) (hφf : φ.comp f = φ) :
    rankOneEnd φ v * f = rankOneEnd φ v := by
  ext x
  have hx := LinearMap.congr_fun hφf x
  simpa [rankOneEnd, Module.End.mul_apply] using congrArg (fun z : ℂ => z • v) hx

/-- Absorbing rank-one projection data split every positive transfer power. -/
private theorem pow_succ_eq_rankOneEnd_add_pow_sub
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : Module.End ℂ V) (φ : V →ₗ[ℂ] ℂ) (v : V)
    (hfv : f v = v) (hφf : φ.comp f = φ) (hφv : φ v = 1) (n : ℕ) :
    f ^ (n + 1) = rankOneEnd φ v + (f - rankOneEnd φ v) ^ (n + 1) := by
  let P := rankOneEnd φ v
  let q := f - P
  have hPP : P * P = P := by
    simpa only [P, pow_two] using rankOneEnd_sq φ v hφv
  have hfP : f * P = P := by
    simpa only [P] using mul_rankOneEnd f φ v hfv
  have hPf : P * f = P := by
    simpa only [P] using rankOneEnd_mul f φ v hφf
  have hPq : P * q = 0 := by rw [show q = f - P by rfl, mul_sub, hPf, hPP, sub_self]
  have hqP : q * P = 0 := by rw [show q = f - P by rfl, sub_mul, hfP, hPP, sub_self]
  have hf : f = P + q := by simp [q]
  change f ^ (n + 1) = P + q ^ (n + 1)
  induction n with
  | zero => simpa using hf
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ, ih, hf, add_mul,
        mul_add, mul_add, hPP, hPq, add_zero, pow_succ q n, mul_assoc, hqP,
        mul_zero, zero_add, pow_succ]
      rfl

/-- Removing a normalized simple fixed projection puts the remaining spectrum in the open disk. -/
private theorem spectrum_sub_rankOneEnd_norm_lt_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (φ : V →ₗ[ℂ] ℂ) (v : V)
    (hφf : φ.comp f = φ) (hφv : φ v = 1)
    (heig : ∀ x, f x = x → ∃ c : ℂ, x = c • v)
    (hspec : ∀ μ ∈ spectrum ℂ f, μ ≠ 1 → ‖μ‖ < 1) :
    ∀ μ ∈ spectrum ℂ (f - rankOneEnd φ v), ‖μ‖ < 1 := by
  let P := rankOneEnd φ v
  let q := f - P
  have hPq : P * q = 0 := by
    rw [show q = f - P by rfl, mul_sub,
      show P * f = P by simpa only [P] using rankOneEnd_mul f φ v hφf,
      show P * P = P by simpa only [P, pow_two] using rankOneEnd_sq φ v hφv,
      sub_self]
  intro μ hμ
  change μ ∈ spectrum ℂ q at hμ
  obtain ⟨x, hx⟩ :=
    (Module.End.HasUnifEigenvalue.of_mem_spectrum hμ).exists_hasUnifEigenvector
  have hqx : q x = μ • x := hx.apply_eq_smul
  by_cases hμ0 : μ = 0
  · simp [hμ0]
  have hPx : P x = 0 := by
    have hpqx : P (q x) = 0 := by
      simpa only [Module.End.mul_apply] using
        congrArg (fun g : Module.End ℂ V => g x) hPq
    have hμPx : μ • P x = 0 := by simpa [hqx] using hpqx
    exact (smul_eq_zero.mp hμPx).resolve_left hμ0
  have hfx : f x = μ • x := by
    simpa only [q, LinearMap.sub_apply, hPx, sub_zero] using hqx
  have hxf : f.HasUnifEigenvector μ 1 x :=
    ⟨Module.End.mem_genEigenspace_one.mpr hfx, hx.2⟩
  have hμspec : μ ∈ spectrum ℂ f :=
    hxf.hasUnifEigenvalue.mem_spectrum
  have hμ1 : μ ≠ 1 := by
    intro hμeq
    have hfixed : f x = x := by simpa [hμeq] using hfx
    obtain ⟨c, rfl⟩ := heig x hfixed
    have hPcv : P (c • v) = c • v := by
      simp [P, rankOneEnd, hφv]
    exact hx.2 (hPcv ▸ hPx)
  exact hspec μ hμspec hμ1

/-- A finite-dimensional endomorphism with a simple normalized fixed direction and a strict gap
has powers converging in operator norm to its rank-one fixed projection. -/
private theorem tendsto_pow_rankOneEnd
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (φ : V →ₗ[ℂ] ℂ) (v : V)
    (hfv : f v = v) (hφf : φ.comp f = φ) (hφv : φ v = 1)
    (heig : ∀ x, f x = x → ∃ c : ℂ, x = c • v)
    (hspec : ∀ μ ∈ spectrum ℂ f, μ ≠ 1 → ‖μ‖ < 1) :
    Tendsto
      (fun n : ℕ => Module.End.toContinuousLinearMap V (f ^ (n + 1)))
      atTop
      (𝓝 (Module.End.toContinuousLinearMap V (rankOneEnd φ v))) := by
  have hvne : v ≠ 0 := by
    intro hv
    rw [hv, map_zero] at hφv
    exact zero_ne_one hφv
  letI : Nontrivial V := ⟨⟨v, 0, hvne⟩⟩
  let E := Module.End.toContinuousLinearMap (𝕜 := ℂ) V
  let P := rankOneEnd φ v
  let q := f - P
  have hqspec : ∀ μ ∈ spectrum ℂ q, ‖μ‖ < 1 := by
    simpa only [q, P] using
      spectrum_sub_rankOneEnd_norm_lt_one f φ v hφf hφv heig hspec
  have hqspecC : ∀ μ ∈ spectrum ℂ (E q), ‖μ‖₊ < (1 : NNReal) := by
    intro μ hμ
    have hμq : μ ∈ spectrum ℂ q := by
      rw [← AlgEquiv.spectrum_eq E q]
      exact hμ
    exact_mod_cast hqspec μ hμq
  have hsr : spectralRadius ℂ (E q) < 1 :=
    spectrum.spectralRadius_lt_of_forall_lt (E q) hqspecC
  have hqpow :
      Tendsto (fun n : ℕ => (E q) ^ n) atTop (𝓝 0) :=
    tendsto_pow_zero_of_spectralRadius_lt_one (E q) hsr
  have hlimit :
      Tendsto (fun n : ℕ => E P + (E q) ^ (n + 1)) atTop (𝓝 (E P)) := by
    simpa using (hqpow.comp (Filter.tendsto_add_atTop_nat 1)).const_add (E P)
  apply hlimit.congr'
  filter_upwards [] with n
  rw [pow_succ_eq_rankOneEnd_add_pow_sub f φ v hfv hφf hφv n]
  simp only [E, P, q, map_add, map_pow]

/-! ## Faithful weighted-trace limit -/

/-- The trace pairing `X ↦ tr(ρX)` as a complex linear functional. -/
private noncomputable def weightedTrace (ρ : CStarMatrix (Fin D) (Fin D) ℂ) :
    CStarMatrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (LinearMap.mulLeft ℂ ρ)

/-- The trace pairing normalized to take the identity matrix to one. -/
private noncomputable def normalizedWeightedTrace
    (ρ : CStarMatrix (Fin D) (Fin D) ℂ) :
    CStarMatrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
  (ρ.trace)⁻¹ • weightedTrace ρ

/-- Weighted trace intertwines the finite Kraus transfer with its dual action. -/
private theorem weightedTrace_finiteKrausMap
    {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (ρ X : CStarMatrix (Fin D) (Fin D) ℂ) :
    weightedTrace ρ (finiteKrausMap A X) =
      ((∑ σ, star (A σ) * ρ * A σ) * X).trace := by
  change (ρ * ∑ σ, A σ * X * star (A σ)).trace =
    ((∑ σ, star (A σ) * ρ * A σ) * X).trace
  rw [Finset.mul_sum, Finset.sum_mul]
  change (Matrix.traceLinearMap (Fin D) ℂ ℂ)
      (∑ σ, ρ * (A σ * X * star (A σ))) =
    (Matrix.traceLinearMap (Fin D) ℂ ℂ)
      (∑ σ, (star (A σ) * ρ * A σ) * X)
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  change (ρ * (A σ * X * star (A σ))).trace =
    ((star (A σ) * ρ * A σ) * X).trace
  calc
    (ρ * (A σ * X * star (A σ))).trace =
        ((ρ * A σ) * X * star (A σ)).trace := by
      congr 1
      noncomm_ring
    _ = (star (A σ) * (ρ * A σ) * X).trace :=
      Matrix.trace_mul_cycle (ρ * A σ) X (star (A σ))
    _ = ((star (A σ) * ρ * A σ) * X).trace := by
      congr 1
      noncomm_ring

/-- A faithful matrix has nonzero trace. -/
private theorem posDef_trace_ne_zero [NeZero D]
    {ρ : CStarMatrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) :
    ρ.trace ≠ 0 :=
  ne_of_gt hρ.trace_pos

/-- The normalized faithful weighted trace takes the identity to one. -/
private theorem normalizedWeightedTrace_one [NeZero D]
    {ρ : CStarMatrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) :
    normalizedWeightedTrace ρ 1 = 1 := by
  rw [normalizedWeightedTrace, LinearMap.smul_apply, weightedTrace]
  change ρ.trace⁻¹ * (ρ * 1).trace = 1
  rw [mul_one, inv_mul_cancel₀ (posDef_trace_ne_zero hρ)]

/-- The faithful dual equation makes normalized weighted trace invariant under the normalized
finite Kraus transfer. -/
private theorem normalizedWeightedTrace_comp_normalized_finiteKrausMap
    [NeZero D] {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (lam : ℂ) (hlam : lam ≠ 0)
    (ρ : CStarMatrix (Fin D) (Fin D) ℂ)
    (hdual : ∑ σ, star (A σ) * ρ * A σ = lam • ρ) :
    (normalizedWeightedTrace ρ).comp (lam⁻¹ • finiteKrausMap A) =
      normalizedWeightedTrace ρ := by
  ext X
  change normalizedWeightedTrace ρ (lam⁻¹ • finiteKrausMap A X) =
    normalizedWeightedTrace ρ X
  simp only [normalizedWeightedTrace, LinearMap.smul_apply, map_smul]
  change lam⁻¹ * (ρ.trace⁻¹ * weightedTrace ρ (finiteKrausMap A X)) =
    ρ.trace⁻¹ * weightedTrace ρ X
  rw [weightedTrace_finiteKrausMap, hdual]
  rw [CStarMatrix.smul_mul]
  change lam⁻¹ * (ρ.trace⁻¹ *
      (Matrix.traceLinearMap (Fin D) ℂ ℂ) (lam • (ρ * X))) =
    ρ.trace⁻¹ * (ρ * X).trace
  rw [show (Matrix.traceLinearMap (Fin D) ℂ ℂ) (lam • (ρ * X)) =
      lam * (ρ * X).trace by
    simpa only [RingHom.id_apply] using
      (Matrix.traceLinearMap (Fin D) ℂ ℂ).map_smul lam (ρ * X)]
  rw [show lam⁻¹ * (ρ.trace⁻¹ * (lam * (ρ * X).trace)) =
      ρ.trace⁻¹ * ((lam⁻¹ * lam) * (ρ * X).trace) by ring,
    inv_mul_cancel₀ hlam, one_mul]

/-- The normalized faithful weighted-trace rank-one map written without private abbreviations. -/
private theorem rankOneEnd_normalizedWeightedTrace
    (ρ : CStarMatrix (Fin D) (Fin D) ℂ) :
    rankOneEnd (normalizedWeightedTrace ρ)
        (1 : CStarMatrix (Fin D) (Fin D) ℂ) =
      (((ρ.trace)⁻¹ •
        (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
          (LinearMap.mulLeft ℂ ρ)).smulRight
            (1 : CStarMatrix (Fin D) (Fin D) ℂ)) := by
  rfl

/-- A normalized finite Kraus transfer with a faithful dual eigenmatrix, simple fixed direction,
and strict spectral gap converges to the normalized weighted-trace rank-one map.

This theorem-specific endpoint is consumed by `MPSTheorem75Choi` to obtain eventual positive
definiteness of transfer-power Choi matrices. -/
theorem tendsto_normalized_finiteKrausMap_pow_weightedTrace [NeZero D]
    {ι : Type*} [Fintype ι]
    (A : ι → CStarMatrix (Fin D) (Fin D) ℂ)
    (lam : ℂ) (hlam : lam ≠ 0)
    (ρ : CStarMatrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hone : finiteKrausMap A 1 =
      lam • (1 : CStarMatrix (Fin D) (Fin D) ℂ))
    (hdual : ∑ σ, star (A σ) * ρ * A σ = lam • ρ)
    (heig : ∀ X, (lam⁻¹ • finiteKrausMap A) X = X →
      ∃ c : ℂ, X = c • (1 : CStarMatrix (Fin D) (Fin D) ℂ))
    (hspec : ∀ μ ∈ spectrum ℂ (lam⁻¹ • finiteKrausMap A),
      μ ≠ 1 → ‖μ‖ < 1) :
    letI : FiniteDimensional ℂ (CStarMatrix (Fin D) (Fin D) ℂ) :=
      CStarMatrix.ofMatrixₗ.finiteDimensional
    Tendsto
        (fun n : ℕ => Module.End.toContinuousLinearMap
          (CStarMatrix (Fin D) (Fin D) ℂ)
          ((lam⁻¹ • finiteKrausMap A) ^ (n + 1)))
        atTop
        (𝓝 (Module.End.toContinuousLinearMap
          (CStarMatrix (Fin D) (Fin D) ℂ)
          (((ρ.trace)⁻¹ •
            (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp
              (LinearMap.mulLeft ℂ ρ)).smulRight
                (1 : CStarMatrix (Fin D) (Fin D) ℂ)))) := by
  letI : FiniteDimensional ℂ (CStarMatrix (Fin D) (Fin D) ℂ) :=
    CStarMatrix.ofMatrixₗ.finiteDimensional
  let f := lam⁻¹ • finiteKrausMap A
  let φ := normalizedWeightedTrace ρ
  have hfixed : f 1 = 1 := by
    simp only [f, LinearMap.smul_apply, hone, inv_smul_smul₀ hlam]
  have hinvariant : φ.comp f = φ := by
    simpa only [f, φ] using
      normalizedWeightedTrace_comp_normalized_finiteKrausMap A lam hlam ρ hdual
  have hφone : φ 1 = 1 := by
    simpa only [φ] using normalizedWeightedTrace_one hρ
  have hlimit :=
    tendsto_pow_rankOneEnd f φ
      (1 : CStarMatrix (Fin D) (Fin D) ℂ)
      hfixed hinvariant hφone heig hspec
  rw [rankOneEnd_normalizedWeightedTrace] at hlimit
  exact hlimit

end LatticeSystem.Quantum.MPSTheorem75.Internal
