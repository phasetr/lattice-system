import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Scalar spherical monomial moments on `S² ⊂ ℝ³` (Tasaki eq. (4.2.58), PR-1)

This module proves the closed form of the **monomial (Dirichlet) moments** of the
rotation-invariant surface measure `volume.toSphere` on `S² ⊂ ℝ³ = EuclideanSpace ℝ (Fin 3)`:

* `sphereMonomialMoment_odd` — if some exponent `k i` is odd then
  `∫_{S²} ∏ i, (n i)^(k i) dσ(n) = 0`;
* `sphereMonomialMoment_even` — if all exponents are even then the moment equals
  `4π · (∏ i, (k i - 1)‼) / ((∑ i, k i) + 1)‼`, where `‼` is `Nat.doubleFactorial`.

These are the scalar substrate consumed (in the operator polynomial expansion of the Anderson-tower
argument) by Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (Springer, GTP),
§4.2.2, **eq. (4.2.58), p.108** (attributed there to "(4.40) of [66]", Koma–Tasaki).  The
double-factorial closed value is load-bearing: the ratio `(M-1)‼ / (M+1)‼ = 1/(M+1)` produces the
`1/(M+1)` coefficient of eq. (4.2.58).

## Proof strategy (Gaussian–polar)

We never build spherical coordinates.  Instead we compute the isotropic Gaussian integral
`∫_{ℝ³} (∏ i, x_i^{k_i}) e^{-‖x‖²/2} dx` in two ways: a Cartesian factorisation over the three axes
(`gaussCartesian`) and a polar factorisation into a sphere moment times a radial Gaussian integral
(`gaussPolar`).  Equating them (`sphereMonomial_mul_halfMoment`) and using the one-dimensional
closed forms yields the result.
-/

open Real Set MeasureTheory
open scoped Nat

namespace LatticeSystem.Math

/-! ## One-dimensional Gaussian moments -/

/-- The one-dimensional half-line Gaussian moment `∫_{r>0} r^n e^{-r²/2} dr`.  It is always positive
and, for even `n`, has the closed value `(n-1)‼ · √(π/2)` (`gaussHalfMoment_two_mul`). -/
noncomputable def gaussHalfMoment (n : ℕ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-t ^ 2 / 2)

/-- The one-dimensional full-line Gaussian moment `∫_ℝ t^n e^{-t²/2} dt`.  It vanishes for odd `n`
and equals `2 · gaussHalfMoment n` for even `n` (`gaussFullMoment_eq`). -/
noncomputable def gaussFullMoment (n : ℕ) : ℝ :=
  ∫ t : ℝ, t ^ n * Real.exp (-t ^ 2 / 2)

/-- The integrand `t ↦ t^n e^{-t²/2}` is integrable over the whole real line (polynomial times a
Gaussian). -/
theorem integrable_pow_mul_gauss (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n * Real.exp (-t ^ 2 / 2)) := by
  have hs : (-1 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) hs
  refine h.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.rpow_natCast]
  congr 1
  ring

/-- The half-line Gaussian moment expressed through the Gamma function via
`integral_rpow_mul_exp_neg_mul_rpow` (`p = 2`, `q = n`, `b = 1/2`). -/
theorem gaussHalfMoment_eq_gamma (n : ℕ) :
    gaussHalfMoment n =
      (1 / 2 : ℝ) ^ (-((n : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((n : ℝ) + 1) / 2) := by
  have hq : (-1 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hrw : (∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-t ^ 2 / 2))
      = ∫ t in Ioi (0 : ℝ), t ^ (n : ℝ) * Real.exp (-(1 / 2) * t ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [Real.rpow_natCast, Real.rpow_two]
    congr 1
    ring
  rw [gaussHalfMoment, hrw,
    integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) hq (by norm_num)]

/-- The positive constant `√(π/2)` appearing in the even Gaussian moments, isolated so the algebra
in `gaussHalfMoment_two_mul` is transparent. -/
theorem sqrt_two_mul_half_mul_sqrt_pi :
    Real.sqrt 2 * (1 / 2) * Real.sqrt π = Real.sqrt (π / 2) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  rw [Real.sqrt_div Real.pi_pos.le, eq_div_iff hs2,
    show Real.sqrt 2 * (1 / 2) * Real.sqrt π * Real.sqrt 2
      = Real.sqrt 2 * Real.sqrt 2 * ((1 / 2) * Real.sqrt π) by ring, h2]
  ring

/-- Closed value of the half-line Gaussian moment at an even index:
`gaussHalfMoment (2 j) = (2 j - 1)‼ · √(π/2)`. -/
theorem gaussHalfMoment_two_mul (j : ℕ) :
    gaussHalfMoment (2 * j) = ((2 * j - 1)‼ : ℝ) * Real.sqrt (π / 2) := by
  rw [gaussHalfMoment_eq_gamma]
  have harg : ((2 * j : ℕ) : ℝ) + 1 = 2 * ((j : ℝ) + 1 / 2) := by push_cast; ring
  have hgamma : Real.Gamma ((((2 * j : ℕ) : ℝ) + 1) / 2) = ((2 * j - 1)‼ : ℝ) * √π / 2 ^ j := by
    rw [harg, show 2 * ((j : ℝ) + 1 / 2) / 2 = (j : ℝ) + 1 / 2 by ring, Real.Gamma_nat_add_half j]
  have hhalf : ∀ y : ℝ, (1 / 2 : ℝ) ^ (-y) = (2 : ℝ) ^ y := by
    intro y
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num),
      ← Real.rpow_neg (by norm_num), neg_neg]
  have hexp : (1 / 2 : ℝ) ^ (-(((2 * j : ℕ) : ℝ) + 1) / 2) = (2 : ℝ) ^ j * Real.sqrt 2 := by
    rw [show -(((2 * j : ℕ) : ℝ) + 1) / 2 = -((j : ℝ) + 1 / 2) by push_cast; ring, hhalf,
      Real.rpow_add (by norm_num), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [hexp, hgamma,
    show (2 : ℝ) ^ j * Real.sqrt 2 * (1 / 2) * (((2 * j - 1)‼ : ℝ) * √π / 2 ^ j)
      = (2 : ℝ) ^ j / 2 ^ j * (Real.sqrt 2 * (1 / 2) * Real.sqrt π) * ((2 * j - 1)‼ : ℝ) by ring,
    div_self (by positivity : (2 : ℝ) ^ j ≠ 0), one_mul, sqrt_two_mul_half_mul_sqrt_pi]
  ring

/-- The half-line Gaussian moment is strictly positive: the integrand is positive on `(0, ∞)`, a set
of positive (indeed infinite) Lebesgue measure. -/
theorem gaussHalfMoment_pos (n : ℕ) : 0 < gaussHalfMoment n := by
  rw [gaussHalfMoment]
  have hfi : IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-t ^ 2 / 2)) (Ioi 0) :=
    (integrable_pow_mul_gauss n).integrableOn
  have hf : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => t ^ n * Real.exp (-t ^ 2 / 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg ht.le n) (Real.exp_pos _).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hf hfi]
  have hsub :
      (Function.support fun t : ℝ => t ^ n * Real.exp (-t ^ 2 / 2)) ∩ Ioi 0 = Ioi 0 := by
    ext t
    refine ⟨fun h => h.2, fun ht => ⟨?_, ht⟩⟩
    exact (mul_pos (pow_pos ht n) (Real.exp_pos _)).ne'
  rw [hsub, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- The full-line Gaussian moment as a signed multiple of the half-line one:
`∫_ℝ t^n e^{-t²/2} dt = (1 + (-1)^n)·∫_{r>0} r^n e^{-r²/2} dr`.  In particular it vanishes for odd
`n` and equals `2·gaussHalfMoment n` for even `n`. -/
theorem gaussFullMoment_eq (n : ℕ) :
    gaussFullMoment n = (1 + (-1) ^ n) * gaussHalfMoment n := by
  have hint := integrable_pow_mul_gauss n
  have hneg : (∫ t in Iic (0 : ℝ), t ^ n * Real.exp (-t ^ 2 / 2))
      = (-1) ^ n * gaussHalfMoment n := by
    have hcv := integral_comp_neg_Iic (0 : ℝ) fun x : ℝ => x ^ n * Real.exp (-x ^ 2 / 2)
    simp only [neg_zero, neg_sq] at hcv
    rw [← gaussHalfMoment] at hcv
    rw [← hcv, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    have hbase : ((-1 : ℝ)) ^ n * ((-t) ^ n * Real.exp (-t ^ 2 / 2))
        = (((-1) * (-t)) ^ n) * Real.exp (-t ^ 2 / 2) := by rw [mul_pow]; ring
    rw [hbase, neg_one_mul, neg_neg]
  rw [gaussFullMoment, ← integral_add_compl measurableSet_Iic hint, compl_Iic, hneg,
    gaussHalfMoment]
  ring

/-! ## Three-dimensional isotropic Gaussian: Cartesian and polar factorisations -/

/-- The isotropic Gaussian monomial integrand on `ℝ³`: `x ↦ (∏ i, x_i^{k_i}) · e^{-‖x‖²/2}`. -/
noncomputable def gaussMonomial (k : Fin 3 → ℕ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (∏ i, (x i) ^ (k i)) * Real.exp (-‖x‖ ^ 2 / 2)

/-- The sum `∑ i, -(x_i)²/2` equals `-‖x‖²/2` for `x ∈ ℝ³`, used to factor the Gaussian across
axes. -/
theorem sum_neg_sq_div_two (x : EuclideanSpace ℝ (Fin 3)) :
    ∑ i, -(x i) ^ 2 / 2 = -‖x‖ ^ 2 / 2 := by
  rw [← Finset.sum_div, Finset.sum_neg_distrib, ← EuclideanSpace.real_norm_sq_eq]

/-- `gaussMonomial` is the pullback along `WithLp.ofLp` of a product of one-dimensional Gaussian
factors, the shape consumed by `Integrable.fintype_prod` and `integral_fintype_prod`. -/
theorem gaussMonomial_comp_ofLp (k : Fin 3 → ℕ) :
    (fun y : Fin 3 → ℝ => ∏ i, (y i) ^ (k i) * Real.exp (-(y i) ^ 2 / 2)) ∘ WithLp.ofLp
      = gaussMonomial k := by
  funext x
  simp only [Function.comp_apply, gaussMonomial]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← sum_neg_sq_div_two x]

/-- The isotropic Gaussian monomial integrand is integrable over `ℝ³`. -/
theorem integrable_gaussMonomial (k : Fin 3 → ℕ) : Integrable (gaussMonomial k) := by
  have hpi : Integrable
      (fun y : Fin 3 → ℝ => ∏ i, (y i) ^ (k i) * Real.exp (-(y i) ^ 2 / 2)) :=
    Integrable.fintype_prod fun i => integrable_pow_mul_gauss (k i)
  rw [← gaussMonomial_comp_ofLp k]
  exact ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding).mpr hpi

/-- Cartesian factorisation of the isotropic Gaussian monomial integral over `ℝ³`. -/
theorem gaussCartesian (k : Fin 3 → ℕ) :
    ∫ x, gaussMonomial k x = ∏ i, gaussFullMoment (k i) := by
  have he := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp'
    (fun y : Fin 3 → ℝ => ∏ i, (y i) ^ (k i) * Real.exp (-(y i) ^ 2 / 2))
  rw [← gaussMonomial_comp_ofLp k,
    show (∫ x : EuclideanSpace ℝ (Fin 3),
        ((fun y : Fin 3 → ℝ => ∏ i, (y i) ^ (k i) * Real.exp (-(y i) ^ 2 / 2)) ∘ WithLp.ofLp) x)
      = ∫ y : Fin 3 → ℝ, ∏ i, (y i) ^ (k i) * Real.exp (-(y i) ^ 2 / 2) from he,
    integral_fintype_prod_volume_eq_prod fun i (t : ℝ) => t ^ (k i) * Real.exp (-t ^ 2 / 2)]
  rfl

/-- The radial integral against `volumeIoiPow 2` unfolds to a Lebesgue integral over `(0, ∞)` with
the Jacobian weight `r²`. -/
theorem integral_volumeIoiPow_two (h : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), h (r : ℝ) ∂Measure.volumeIoiPow 2
      = ∫ r in Ioi (0 : ℝ), (r : ℝ) ^ 2 * h r := by
  have hmeas : Measurable (fun r : Ioi (0 : ℝ) => Real.toNNReal ((r : ℝ) ^ 2)) :=
    (measurable_subtype_coe.pow_const 2).real_toNNReal
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul hmeas,
    integral_subtype_comap measurableSet_Ioi fun a : ℝ => Real.toNNReal (a ^ 2) • h a]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hx) 2), smul_eq_mul]

/-- Polar decomposition of an integrable function over `ℝ³` into sphere and radial integrals. -/
theorem integral_gauss_polar (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : Integrable g) :
    ∫ x, g x
      = ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          ∫ r : Ioi (0 : ℝ), g ((r : ℝ) • (ω : EuclideanSpace ℝ (Fin 3)))
            ∂Measure.volumeIoiPow 2 ∂volume.toSphere := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1 = 2 := by
    rw [finrank_euclideanSpace_fin]
  have hmp0 := (volume :
    Measure (EuclideanSpace ℝ (Fin 3))).measurePreserving_homeomorphUnitSphereProd
  rw [hdim] at hmp0
  set F := (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Ioi (0 : ℝ) =>
    g ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin 3)))) with hF
  have hcomp : ∀ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
      g (x : EuclideanSpace ℝ (Fin 3))
        = F (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3)) x) := by
    intro x
    have hx : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 := x.2
    simp only [hF, homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]
  have hFint : Integrable F (volume.toSphere.prod (Measure.volumeIoiPow 2)) := by
    rw [← hmp0.integrable_comp_emb
      (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3))).measurableEmbedding]
    have hcomp' : (F ∘ homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3)))
        = g ∘ (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) → _) := by
      funext x; exact (hcomp x).symm
    rw [hcomp', ← integrableOn_iff_comap_subtypeVal
      (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin 3))).compl]
    exact hg.integrableOn
  calc ∫ x, g x
      = ∫ x in ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))), g x := by rw [restrict_compl_singleton]
    _ = ∫ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))), g (x : EuclideanSpace ℝ (Fin 3))
          ∂(Measure.comap Subtype.val volume) :=
        (integral_subtype_comap (measurableSet_singleton _).compl g).symm
    _ = ∫ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))),
          F (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3)) x)
          ∂(Measure.comap Subtype.val volume) :=
        integral_congr_ae (Filter.Eventually.of_forall hcomp)
    _ = ∫ p, F p ∂(volume.toSphere.prod (Measure.volumeIoiPow 2)) :=
        hmp0.integral_comp
          (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 3))).measurableEmbedding F
    _ = ∫ ω, ∫ r, F (ω, r) ∂Measure.volumeIoiPow 2 ∂volume.toSphere := integral_prod F hFint

/-- Polar factorisation: the isotropic Gaussian monomial integral over `ℝ³` equals the sphere
monomial moment times the radial Gaussian moment `gaussHalfMoment (M+2)`, `M = ∑ i, k i`. -/
theorem gaussPolar (k : Fin 3 → ℕ) :
    ∫ x, gaussMonomial k x
      = (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
            ∏ i, ((ω : EuclideanSpace ℝ (Fin 3)) i) ^ (k i) ∂volume.toSphere)
        * gaussHalfMoment ((∑ i, k i) + 2) := by
  rw [integral_gauss_polar (gaussMonomial k) (integrable_gaussMonomial k)]
  have hinner : ∀ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (∫ r : Ioi (0 : ℝ), gaussMonomial k ((r : ℝ) • (ω : EuclideanSpace ℝ (Fin 3)))
          ∂Measure.volumeIoiPow 2)
        = (∏ i, ((ω : EuclideanSpace ℝ (Fin 3)) i) ^ (k i)) * gaussHalfMoment ((∑ i, k i) + 2) := by
    intro ω
    have hnorm : ∀ r : Ioi (0 : ℝ), ‖((r : ℝ) • (ω : EuclideanSpace ℝ (Fin 3)))‖ = (r : ℝ) := by
      intro r
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.2, mem_sphere_zero_iff_norm.mp ω.2, mul_one]
    have hval : ∀ r : Ioi (0 : ℝ),
        gaussMonomial k ((r : ℝ) • (ω : EuclideanSpace ℝ (Fin 3)))
          = (∏ i, ((ω : EuclideanSpace ℝ (Fin 3)) i) ^ (k i))
            * ((r : ℝ) ^ (∑ i, k i) * Real.exp (-(r : ℝ) ^ 2 / 2)) := by
      intro r
      simp only [gaussMonomial]
      rw [hnorm r]
      have hprod : (∏ i, ((r : ℝ) • (ω : EuclideanSpace ℝ (Fin 3))) i ^ (k i))
          = (r : ℝ) ^ (∑ i, k i) * ∏ i, ((ω : EuclideanSpace ℝ (Fin 3)) i) ^ (k i) := by
        simp only [PiLp.smul_apply, smul_eq_mul, mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rw [hprod]; ring
    calc ∫ r : Ioi (0 : ℝ), gaussMonomial k ((r : ℝ) • (ω : EuclideanSpace ℝ (Fin 3)))
            ∂Measure.volumeIoiPow 2
        = ∫ r : Ioi (0 : ℝ), (∏ i, ((ω : EuclideanSpace ℝ (Fin 3)) i) ^ (k i))
            * ((r : ℝ) ^ (∑ i, k i) * Real.exp (-(r : ℝ) ^ 2 / 2)) ∂Measure.volumeIoiPow 2 :=
          integral_congr_ae (Filter.Eventually.of_forall hval)
      _ = (∏ i, ((ω : EuclideanSpace ℝ (Fin 3)) i) ^ (k i))
            * ∫ r : Ioi (0 : ℝ), (r : ℝ) ^ (∑ i, k i) * Real.exp (-(r : ℝ) ^ 2 / 2)
              ∂Measure.volumeIoiPow 2 := by rw [integral_const_mul]
      _ = (∏ i, ((ω : EuclideanSpace ℝ (Fin 3)) i) ^ (k i))
            * ∫ r in Ioi (0 : ℝ),
                (r : ℝ) ^ 2 * ((r : ℝ) ^ (∑ i, k i) * Real.exp (-(r : ℝ) ^ 2 / 2)) := by
          rw [integral_volumeIoiPow_two
            fun t : ℝ => t ^ (∑ i, k i) * Real.exp (-t ^ 2 / 2)]
      _ = (∏ i, ((ω : EuclideanSpace ℝ (Fin 3)) i) ^ (k i)) * gaussHalfMoment ((∑ i, k i) + 2) := by
          rw [gaussHalfMoment]
          congr 1
          refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
          rw [← mul_assoc, ← pow_add, Nat.add_comm 2 (∑ i, k i)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), ← integral_mul_const]

/-- Master identity: the sphere monomial moment times the radial Gaussian moment equals the product
of the axial full-line Gaussian moments. -/
theorem sphereMonomial_mul_halfMoment (k : Fin 3 → ℕ) :
    (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          ∏ i, ((ω : EuclideanSpace ℝ (Fin 3)) i) ^ (k i) ∂volume.toSphere)
        * gaussHalfMoment ((∑ i, k i) + 2)
      = ∏ i, gaussFullMoment (k i) := by
  rw [← gaussPolar]; exact gaussCartesian k

/-! ## Public spherical monomial moments (Tasaki eq. (4.2.58)) -/

/-- **Odd vanishing.** If some exponent `k i` is odd, the sphere monomial moment vanishes
(Tasaki eq. (4.2.58), odd case). -/
theorem sphereMonomialMoment_odd (k : Fin 3 → ℕ) (h : ∃ i, Odd (k i)) :
    ∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∏ i, ((n : EuclideanSpace ℝ (Fin 3)) i) ^ (k i) ∂volume.toSphere = 0 := by
  obtain ⟨i, hi⟩ := h
  have hmaster := sphereMonomial_mul_halfMoment k
  have hzero : ∏ i, gaussFullMoment (k i) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [gaussFullMoment_eq, Odd.neg_one_pow hi]
    ring
  rw [hzero] at hmaster
  exact (mul_eq_zero.mp hmaster).resolve_right (gaussHalfMoment_pos _).ne'

/-- **Even closed form.** If all exponents `k i` are even, the sphere monomial moment equals
`4π · (∏ i, (k i - 1)‼) / ((∑ i, k i) + 1)‼` (Tasaki eq. (4.2.58), even case). -/
theorem sphereMonomialMoment_even (k : Fin 3 → ℕ) (h : ∀ i, Even (k i)) :
    ∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∏ i, ((n : EuclideanSpace ℝ (Fin 3)) i) ^ (k i) ∂volume.toSphere
      = 4 * Real.pi * ((∏ i, ((k i - 1)‼) : ℕ) : ℝ) / (((∑ i, k i) + 1)‼ : ℝ) := by
  have hmaster := sphereMonomial_mul_halfMoment k
  have heM : Even (∑ i, k i) :=
    even_iff_two_dvd.mpr (Finset.dvd_sum fun i _ => (h i).two_dvd)
  obtain ⟨J, hJ⟩ := heM
  have hMJ : ∑ i, k i = 2 * J := by omega
  have hhalfM : gaussHalfMoment ((∑ i, k i) + 2)
      = ((((∑ i, k i) + 1)‼ : ℕ) : ℝ) * Real.sqrt (π / 2) := by
    rw [hMJ, show 2 * J + 2 = 2 * (J + 1) by ring, gaussHalfMoment_two_mul]
    congr 2
  have hfac : ∀ i, gaussFullMoment (k i) = 2 * ((k i - 1)‼ : ℝ) * Real.sqrt (π / 2) := by
    intro i
    obtain ⟨j, hj⟩ := h i
    have hkj : k i = 2 * j := by omega
    rw [gaussFullMoment_eq, hkj, gaussHalfMoment_two_mul, pow_mul, neg_one_sq, one_pow]
    ring
  have hprodfull : ∏ i, gaussFullMoment (k i)
      = 8 * (∏ i, ((k i - 1)‼ : ℝ)) * (Real.sqrt (π / 2)) ^ 3 := by
    rw [Finset.prod_congr rfl fun i _ => hfac i]
    have hrw : ∀ i, (2 : ℝ) * ((k i - 1)‼ : ℝ) * Real.sqrt (π / 2)
        = ((k i - 1)‼ : ℝ) * (2 * Real.sqrt (π / 2)) := fun i => by ring
    rw [Finset.prod_congr rfl fun i _ => hrw i, Finset.prod_mul_distrib, Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_fin]
    ring
  rw [hhalfM, hprodfull] at hmaster
  have hden : ((((∑ i, k i) + 1)‼ : ℕ) : ℝ) * Real.sqrt (π / 2) ≠ 0 := by positivity
  have key := eq_div_of_mul_eq hden hmaster
  rw [key, ← Nat.cast_prod]
  have hsq : Real.sqrt (π / 2) ^ 3 = (π / 2) * Real.sqrt (π / 2) := by
    rw [pow_succ, pow_two, Real.mul_self_sqrt (by positivity)]
  rw [hsq]
  have hs2 : Real.sqrt (π / 2) ≠ 0 := by positivity
  have hd2 : ((((∑ i, k i) + 1)‼ : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end LatticeSystem.Math
