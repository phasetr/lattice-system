import LatticeSystem.Quantum.SpinS.AndersonTowerSphereVecRemainder
import LatticeSystem.Quantum.SpinS.AndersonTowerSphereReduce
import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSqMoment

/-!
# Tasaki §4.2.2 Proposition 4.10 (PR-6c-i): analytic parts of the final discharge

The self-contained analytic sub-lemmas feeding the final discharge of the sphere-average ground
state (Proposition 4.10).  They convert the *un-normalized* operator remainder bound of PR-6b into a
distance bound between the *normalized* sphere average and the normalized `(ô²)ʲ` tower term, ready
for the diagonal limit assembled in PR-6c-ii.

* **unit-vector perturbation** (`sqrt_vecNormSqRe_unitNormalize_sub_le`): for `w ≠ 0`,
  `‖â − ŵ‖ ≤ 2 ‖a − w‖ / ‖w‖` in the `L²` norm `√(vecNormSqRe ·)`.  The elementary normed-space
  bound `‖a/‖a‖ − w/‖w‖‖ ≤ 2 ‖a − w‖/‖w‖`, transported through the `WithLp` bridge.
* **triangle inequality** (`sqrt_vecNormSqRe_sub_triangle`): the `L²`-norm triangle inequality
  `√(vecNormSqRe (a − c)) ≤ √(vecNormSqRe (a − b)) + √(vecNormSqRe (b − c))`.
* **first-term bound** (`sphereAverage_op_unitNormalize_sub_le`): the analytic heart.  For `j ≥ 1`
  and a long-range-ordered `Φ`, the normalized sphere integral `∫_{S²} (Ô_L^n)^{2j}` and the
  normalized `(ô²)ʲ` tower term differ, in `L²` norm, by at most a `Φ`-independent constant divided
  by the volume — the moment lower bound `R_{2j} ≥ (q₀ (L^d)²)^{2j} R_0` cancels the norm of `Φ`.
  This is the per-volume estimate whose `L ↑ ∞` limit and diagonal assembly are PR-6c-ii.

The positive-scalar absorption (`unitNormalize_ofReal_smul`), the norm identity
`‖(ô²)ʲ Φ‖² = R_{2j}` (`vecNormSqRe_orderSqPow_mulVec`) and the capped diagonal
(`diagonal_tendsto_zero_capped`) are supplied by the modules they naturally belong to and consumed
here.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Proposition 4.10, eqs. (4.2.58)–(4.2.61), pp. 108–109.
-/

namespace LatticeSystem.Quantum

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Elementary scalar and normed-space perturbation bounds -/

/-- **Scalar reciprocal-difference bound**: `|α⁻¹ − ω⁻¹| · α ≤ |α − ω| / ω` for `0 ≤ α`, `0 < ω`.
For `α > 0` it is an equality (`α⁻¹ − ω⁻¹ = (ω − α)/(αω)`); for `α = 0` both sides collapse.  The
scalar core of the unit-vector perturbation bound. -/
private theorem inv_sub_inv_mul_abs_le {α ω : ℝ} (hα : 0 ≤ α) (hω : 0 < ω) :
    |α⁻¹ - ω⁻¹| * α ≤ |α - ω| / ω := by
  rcases hα.lt_or_eq with hpos | h
  · rw [inv_sub_inv hpos.ne' hω.ne', abs_div, abs_sub_comm ω α,
      abs_of_pos (mul_pos hpos hω), div_mul_eq_mul_div]
    apply le_of_eq
    rw [div_eq_div_iff (mul_pos hpos hω).ne' hω.ne']
    ring
  · rw [← h]; simp only [mul_zero]; positivity

/-- **Unit-vector perturbation bound in a complex normed space**: for `W ≠ 0`,
`‖‖A‖⁻¹ • A − ‖W‖⁻¹ • W‖ ≤ 2 ‖A − W‖ / ‖W‖`.  Decompose
`‖A‖⁻¹ • A − ‖W‖⁻¹ • W = ‖W‖⁻¹ • (A − W) + (‖A‖⁻¹ − ‖W‖⁻¹) • A`; the first summand contributes
`‖A − W‖/‖W‖`, the second `|‖A‖⁻¹ − ‖W‖⁻¹| · ‖A‖ ≤ ‖A − W‖/‖W‖` by `inv_sub_inv_mul_abs_le` and the
reverse triangle inequality. -/
private theorem norm_unit_perturbation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A W : E) (hW : W ≠ 0) :
    ‖((‖A‖ : ℝ) : ℂ)⁻¹ • A - ((‖W‖ : ℝ) : ℂ)⁻¹ • W‖ ≤ 2 * ‖A - W‖ / ‖W‖ := by
  have hω : 0 < ‖W‖ := norm_pos_iff.mpr hW
  have hdecomp : ((‖A‖ : ℝ) : ℂ)⁻¹ • A - ((‖W‖ : ℝ) : ℂ)⁻¹ • W
      = ((‖W‖ : ℝ) : ℂ)⁻¹ • (A - W)
        + (((‖A‖ : ℝ) : ℂ)⁻¹ - ((‖W‖ : ℝ) : ℂ)⁻¹) • A := by
    module
  rw [hdecomp]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖((‖W‖ : ℝ) : ℂ)⁻¹ • (A - W)‖ = ‖A - W‖ / ‖W‖ := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_eq_inv_mul]
  have hsc : ((‖A‖ : ℝ) : ℂ)⁻¹ - ((‖W‖ : ℝ) : ℂ)⁻¹ = ((‖A‖⁻¹ - ‖W‖⁻¹ : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : ‖(((‖A‖ : ℝ) : ℂ)⁻¹ - ((‖W‖ : ℝ) : ℂ)⁻¹) • A‖ = |‖A‖⁻¹ - ‖W‖⁻¹| * ‖A‖ := by
    rw [norm_smul, hsc, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2]
  have hscal : |‖A‖⁻¹ - ‖W‖⁻¹| * ‖A‖ ≤ ‖A - W‖ / ‖W‖ := by
    refine le_trans (inv_sub_inv_mul_abs_le (norm_nonneg _) hω) ?_
    gcongr
    exact abs_norm_sub_norm_le A W
  have h2mul : 2 * ‖A - W‖ / ‖W‖ = ‖A - W‖ / ‖W‖ + ‖A - W‖ / ‖W‖ := by ring
  rw [h2mul]
  linarith [hscal]

/-! ### `L²`-norm perturbation and triangle inequalities for `vecNormSqRe` -/

/-- **`L²`-norm unit-vector perturbation bound** (Proposition 4.10, normalization step): for
`w ≠ 0`,
`√(vecNormSqRe (unitNormalize a − unitNormalize w)) ≤ 2 √(vecNormSqRe (a − w)) / √(vecNormSqRe w)`.
The `vecNormSqRe`/`unitNormalize` incarnation of `norm_unit_perturbation`, transported through the
`WithLp` bridge `sqrt_vecNormSqRe_eq_toLp_norm`. -/
theorem sqrt_vecNormSqRe_unitNormalize_sub_le (a w : (Λ → Fin (N + 1)) → ℂ) (hw : w ≠ 0) :
    Real.sqrt (vecNormSqRe (unitNormalize a - unitNormalize w))
      ≤ 2 * Real.sqrt (vecNormSqRe (a - w)) / Real.sqrt (vecNormSqRe w) := by
  set A := (WithLp.toLp 2 a : EuclideanSpace ℂ (Λ → Fin (N + 1))) with hA
  set W := (WithLp.toLp 2 w : EuclideanSpace ℂ (Λ → Fin (N + 1))) with hW
  have hWne : W ≠ 0 := by rw [hW, ne_eq, WithLp.toLp_eq_zero]; exact hw
  have hlhs : Real.sqrt (vecNormSqRe (unitNormalize a - unitNormalize w))
      = ‖((‖A‖ : ℝ) : ℂ)⁻¹ • A - ((‖W‖ : ℝ) : ℂ)⁻¹ • W‖ := by
    rw [sqrt_vecNormSqRe_eq_toLp_norm]
    congr 1
    simp only [unitNormalize, WithLp.toLp_sub, WithLp.toLp_smul]
    rw [sqrt_vecNormSqRe_eq_toLp_norm a, sqrt_vecNormSqRe_eq_toLp_norm w, ← hA, ← hW]
  have haw : Real.sqrt (vecNormSqRe (a - w)) = ‖A - W‖ := by
    rw [sqrt_vecNormSqRe_eq_toLp_norm, WithLp.toLp_sub, ← hA, ← hW]
  have hww : Real.sqrt (vecNormSqRe w) = ‖W‖ := by rw [sqrt_vecNormSqRe_eq_toLp_norm, ← hW]
  rw [hlhs, haw, hww]
  exact norm_unit_perturbation A W hWne

/-- **`L²`-norm triangle inequality** for `vecNormSqRe`:
`√(vecNormSqRe (a − c)) ≤ √(vecNormSqRe (a − b)) + √(vecNormSqRe (b − c))`.  Transport the
Euclidean `L²`-norm triangle inequality (`dist_triangle`) through the `WithLp` bridge. -/
theorem sqrt_vecNormSqRe_sub_triangle (a b c : (Λ → Fin (N + 1)) → ℂ) :
    Real.sqrt (vecNormSqRe (a - c))
      ≤ Real.sqrt (vecNormSqRe (a - b)) + Real.sqrt (vecNormSqRe (b - c)) := by
  rw [sqrt_vecNormSqRe_eq_toLp_norm, sqrt_vecNormSqRe_eq_toLp_norm, sqrt_vecNormSqRe_eq_toLp_norm,
    WithLp.toLp_sub, WithLp.toLp_sub, WithLp.toLp_sub, ← dist_eq_norm, ← dist_eq_norm,
    ← dist_eq_norm]
  exact dist_triangle _ _ _

/-! ### First-term bound: normalized sphere integral vs normalized `(ô²)ʲ` tower term -/

/-- **First-term per-volume bound** (Tasaki §4.2.2, Proposition 4.10, PR-6c-i core).  For `j ≥ 1`
and a nonzero long-range-ordered `Φ`, the normalized even sphere integral
`∫_{S²}(Ô_L^n)^{2j} dσ(n)` and the normalized `(ô²)ʲ` tower term are `L²`-close:

`√(vecNormSqRe (unitNormalize(Op_{2j} Φ) − unitNormalize((ô²)ʲ Φ)))
  ≤ 2 · cartPinchVecPoly j · (L^d · N)^{2j−1} / ((4π/(2j+1)) · (q₀ (L^d)²)ʲ)`.

The right-hand side is **independent of `Φ`** (the factor `√(vecNormSqRe Φ)` cancels): the
un-normalized operator remainder is banded by PR-6b (`sphereAverage_orderSq_vecRemainder_le`), the
positive prefactor `4π/(2j+1)` in front of `(ô²)ʲ Φ` is absorbed by the normalization
(`unitNormalize_ofReal_smul`) after the perturbation bound
(`sqrt_vecNormSqRe_unitNormalize_sub_le`), and the normalization denominator `‖(ô²)ʲ Φ‖ = √R_{2j}`
is bounded below by the long-range-order moment lower bound (`orderSqMoment_ge`,
`vecNormSqRe_orderSqPow_mulVec`).  Since `(2j−1) − 2j = −1`, the volume `(L^d)` appears to the power
`−1`, so PR-6c-ii turns this into a vanishing sequence. -/
theorem sphereAverage_op_unitNormalize_sub_le (d L N j : ℕ) [NeZero L] (hN : 1 ≤ N) (hj : 1 ≤ j)
    {q₀ : ℝ} (hq₀ : 0 < q₀) (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (hΦ : Φ ≠ 0)
    (hlro : q₀ ≤ (star Φ ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
        staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ)).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)) :
    Real.sqrt (vecNormSqRe
        (unitNormalize ((∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
            (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) (torusParitySublattice d L) N)
              ^ (2 * j) ∂volume.toSphere).mulVec Φ)
          - unitNormalize ((orderSqOp (torusParitySublattice d L) N ^ j).mulVec Φ)))
      ≤ 2 * cartPinchVecPoly j * ((L : ℝ) ^ d * N) ^ (2 * j - 1)
          / (4 * Real.pi / (2 * j + 1) * (q₀ * ((L : ℝ) ^ d) ^ 2) ^ j) := by
  have hpi := Real.pi_pos
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := pow_pos hLpos d
  have hcj : (0 : ℝ) < 4 * Real.pi / (2 * j + 1) := by positivity
  have hqV2pos : (0 : ℝ) < q₀ * ((L : ℝ) ^ d) ^ 2 := by positivity
  have hR0pos : 0 < vecNormSqRe Φ := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  have hs : Real.sqrt (vecNormSqRe Φ) ≠ 0 := (Real.sqrt_pos.mpr hR0pos).ne'
  -- the un-normalized `(ô²)ʲ` tower term `u`, its rescaling `w`, and the sphere integral `opv`
  set u := (orderSqOp (torusParitySublattice d L) N ^ j).mulVec Φ with hu
  set w := ((4 * Real.pi / (2 * j + 1) : ℝ) : ℂ) • u with hwdef
  set opv := (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) (torusParitySublattice d L) N)
        ^ (2 * j) ∂volume.toSphere).mulVec Φ with hopv
  -- `R_0 = orderSqMoment 0`, and the moment lower bound `R_{2j} ≥ (q₀ V²)^{2j} R_0`
  have hR0eq : orderSqMoment d L N Φ 0 = vecNormSqRe Φ := by
    rw [orderSqMoment, pow_zero, Matrix.one_mulVec, vecNormSqRe]
  have hmom : (q₀ * ((L : ℝ) ^ d) ^ 2) ^ (2 * j) * orderSqMoment d L N Φ 0
      ≤ orderSqMoment d L N Φ (2 * j) := orderSqMoment_ge d L N Φ hΦ hq₀.le hlro (2 * j)
  -- `‖u‖² = R_{2j} > 0`, so `u ≠ 0` and `w ≠ 0`
  have huvsq : vecNormSqRe u = orderSqMoment d L N Φ (2 * j) := by
    rw [hu]; exact vecNormSqRe_orderSqPow_mulVec d L N j Φ
  have hupos : 0 < vecNormSqRe u := by
    rw [huvsq]
    refine lt_of_lt_of_le ?_ hmom
    rw [hR0eq]; exact mul_pos (pow_pos hqV2pos (2 * j)) hR0pos
  have huneq : u ≠ 0 := by
    intro h; rw [h] at hupos
    simp only [vecNormSqRe, star_zero, zero_dotProduct, Complex.zero_re] at hupos
    exact lt_irrefl 0 hupos
  have hwne : w ≠ 0 := by
    rw [hwdef]
    exact smul_ne_zero (Complex.ofReal_ne_zero.mpr hcj.ne') huneq
  -- rescaling identity `unitNormalize u = unitNormalize w`
  have hnorm_uw : unitNormalize u = unitNormalize w := by
    rw [hwdef]; exact (unitNormalize_ofReal_smul hcj u).symm
  -- `‖w‖ = (4π/(2j+1)) √R_{2j}`
  have hwnorm : vecNormSqRe w = (4 * Real.pi / (2 * j + 1)) ^ 2 * vecNormSqRe u := by
    rw [hwdef]
    unfold vecNormSqRe
    rw [star_smul_dotProduct_smul, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  have hwsqrt : Real.sqrt (vecNormSqRe w)
      = 4 * Real.pi / (2 * j + 1) * Real.sqrt (orderSqMoment d L N Φ (2 * j)) := by
    rw [hwnorm, huvsq, Real.sqrt_mul (by positivity), Real.sqrt_sq hcj.le]
  -- moment lower bound in square-root form: `√R_{2j} ≥ (q₀ V²)ʲ √R_0`
  have hsqrtR2j : (q₀ * ((L : ℝ) ^ d) ^ 2) ^ j * Real.sqrt (vecNormSqRe Φ)
      ≤ Real.sqrt (orderSqMoment d L N Φ (2 * j)) := by
    calc (q₀ * ((L : ℝ) ^ d) ^ 2) ^ j * Real.sqrt (vecNormSqRe Φ)
        = Real.sqrt (((q₀ * ((L : ℝ) ^ d) ^ 2) ^ j) ^ 2 * orderSqMoment d L N Φ 0) := by
          rw [hR0eq, Real.sqrt_mul (by positivity), Real.sqrt_sq (pow_nonneg hqV2pos.le j)]
      _ = Real.sqrt ((q₀ * ((L : ℝ) ^ d) ^ 2) ^ (2 * j) * orderSqMoment d L N Φ 0) := by
          rw [← pow_mul, Nat.mul_comm j 2]
      _ ≤ Real.sqrt (orderSqMoment d L N Φ (2 * j)) := Real.sqrt_le_sqrt hmom
  -- PR-6b operator remainder band, with `Fintype.card = L^d`
  have h6b : Real.sqrt (vecNormSqRe (opv - w))
      ≤ cartPinchVecPoly j * ((L : ℝ) ^ d * N) ^ (2 * j - 1) * Real.sqrt (vecNormSqRe Φ) := by
    have h := sphereAverage_orderSq_vecRemainder_le (torusParitySublattice d L) hN Φ j
    have hscaleq : (4 * Real.pi / (2 * j + 1) : ℂ) = ((4 * Real.pi / (2 * j + 1) : ℝ) : ℂ) := by
      push_cast; ring
    have hcast : (4 * Real.pi / (2 * j + 1) : ℂ) • u = w := by rw [hwdef, hscaleq]
    rw [card_hypercubicTorus d L, Nat.cast_pow, ← hu, hcast, ← hopv] at h
    exact h
  -- positivity of `√‖w‖` and its long-range-order lower bound
  have hvwpos : 0 < vecNormSqRe w := by rw [hwnorm]; exact mul_pos (by positivity) hupos
  have hwpos : 0 < Real.sqrt (vecNormSqRe w) := Real.sqrt_pos.mpr hvwpos
  have hwlb : 4 * Real.pi / (2 * j + 1)
        * ((q₀ * ((L : ℝ) ^ d) ^ 2) ^ j * Real.sqrt (vecNormSqRe Φ))
      ≤ Real.sqrt (vecNormSqRe w) := by
    rw [hwsqrt]; exact mul_le_mul_of_nonneg_left hsqrtR2j hcj.le
  -- `cartPinchVecPoly j ≥ 0`, hence the (`Φ`-independent) right-hand side is nonnegative
  have hcartnn : 0 ≤ cartPinchVecPoly j := by
    rw [cartPinchVecPoly]
    refine mul_nonneg (add_nonneg (Finset.sum_nonneg (fun f _ => sphereMonomialMoment_nonneg _))
      (by positivity)) (by positivity)
  have hRHSnn : 0 ≤ 2 * cartPinchVecPoly j * ((L : ℝ) ^ d * N) ^ (2 * j - 1)
      / (4 * Real.pi / (2 * j + 1) * (q₀ * ((L : ℝ) ^ d) ^ 2) ^ j) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) hcartnn) (by positivity)
    · exact (mul_pos hcj (pow_pos hqV2pos j)).le
  have hden2ne : 4 * Real.pi / (2 * j + 1) * (q₀ * ((L : ℝ) ^ d) ^ 2) ^ j ≠ 0 :=
    (mul_pos hcj (pow_pos hqV2pos j)).ne'
  -- assemble: perturbation bound, then bound numerator (PR-6b) and denominator (moment bound)
  rw [hnorm_uw]
  refine le_trans (sqrt_vecNormSqRe_unitNormalize_sub_le opv w hwne) ?_
  rw [div_le_iff₀ hwpos]
  refine le_trans (mul_le_mul_of_nonneg_left h6b (by norm_num)) ?_
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hwlb hRHSnn)
  field_simp

end LatticeSystem.Quantum
