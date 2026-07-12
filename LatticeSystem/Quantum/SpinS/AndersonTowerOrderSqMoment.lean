import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSq
import LatticeSystem.Math.Analysis.RealLogConvexSequence

/-!
# Tasaki §4.2.2 Proposition 4.10 (PR-4a): the `ô²`-moment lower bound

The squared-order-operator moments `R_k := ⟨Φ, (ô²)^k Φ⟩` and their long-range-order lower bound

`R_m ≥ (q₀ · (L^d)²)^m · R_0`   (`R_0 = ⟨Φ, Φ⟩ = ‖Φ‖²`)

driving the sphere-average relative-close estimate of Proposition 4.10.  The derivation is the
verbatim `ô²`-lift of the Theorem 4.9 `p̂`-moment machinery, in three source-independent steps:

* **log-convexity** `R_{k+1}² ≤ R_k · R_{k+2}` (`orderSqMoment_sq_le`): `ô² = orderSqOp` is
  Hermitian and positive-semidefinite, so the moments obey the positive-semidefinite Cauchy–Schwarz
  (`posSemidef_re_dotProduct_mulVec_sq_le`), read through `hermitian_pow_dotProduct_split`;
* **base** `R_1 ≥ q₀ · (L^d)² · R_0` (`orderSqMoment_one_ge`): the transverse/longitudinal split
  `ô² = (L^d)² · p̂ + (ô^{(3)})²` (`orderSqOp_eq_smul_staggeredPhatS_add_sq`) drops the
  positive-semidefinite `(L^d)² · p̂` and applies the long-range-order hypothesis
  `q₀ ≤ ⟨(ô^{(3)})²⟩ / (‖Φ‖² (L^d)²)` to the surviving longitudinal part — no isotropy required;
* **telescoping** (`orderSqMoment_ge`): the abstract `real_logConvex_geometric_lower` iterates the
  log-convexity from the base ratio to the geometric lower bound `R_m ≥ (q₀ (L^d)²)^m R_0`.

Only the `q₀` one-sided lower bound is established here; the sphere-average relative-close estimate
and its `L ↑ ∞` limit are the sequel PR-4b.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Proposition 4.10, eqs. (4.2.31), (4.2.35)–(4.2.37), (4.2.58)–(4.2.59), pp. 105–108.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-! ### Hermiticity and positive-semidefiniteness of `ô²` on the torus -/

/-- **`ô²` is Hermitian on the hypercubic torus**: via the split
`ô² = (L^d)² · p̂ + (ô^{(3)})²`, both summands are Hermitian (`p̂` with a real scalar, and the
Hermitian square `(ô^{(3)})² = staggeredOrderOpS²`). -/
theorem orderSqOp_torus_isHermitian (d L N : ℕ) [NeZero L] :
    (orderSqOp (torusParitySublattice d L) N).IsHermitian := by
  rw [orderSqOp_eq_smul_staggeredPhatS_add_sq]
  refine Matrix.IsHermitian.add ((staggeredPhatS_isHermitian d L N).smul ?_)
    ((staggeredOrderOpS_isHermitian _ N).pow 2)
  rw [isSelfAdjoint_iff, Complex.star_def, map_pow, map_pow, Complex.conj_natCast]

/-- **`ô²` is positive-semidefinite on the hypercubic torus**: via the split, it is the sum of the
positive-semidefinite `(L^d)² · p̂` (`staggeredPhatS_posSemidef`, real scalar `(L^d)² ≥ 0`) and the
Hermitian square `(ô^{(3)})²`. -/
theorem orderSqOp_torus_posSemidef (d L N : ℕ) [NeZero L] :
    (orderSqOp (torusParitySublattice d L) N).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (orderSqOp_torus_isHermitian d L N)
    (fun Φ => ?_)
  have hsqpsd : (staggeredOrderOpS (torusParitySublattice d L) N ^ 2).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self
      (staggeredOrderOpS (torusParitySublattice d L) N)
    rwa [(staggeredOrderOpS_isHermitian _ N).eq, ← pow_two] at h
  have hV2 : (0 : ℂ) ≤ ((L : ℂ) ^ d) ^ 2 := by
    rw [show (((L : ℂ) ^ d) ^ 2) = ((((L : ℝ) ^ d) ^ 2 : ℝ) : ℂ) from by push_cast; ring]
    exact Complex.zero_le_real.mpr (by positivity)
  rw [orderSqOp_eq_smul_staggeredPhatS_add_sq, Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact add_nonneg (mul_nonneg hV2 ((staggeredPhatS_posSemidef d L N).dotProduct_mulVec_nonneg Φ))
    (hsqpsd.dotProduct_mulVec_nonneg Φ)

/-- **Powers of `ô²` are positive-semidefinite** for every `k` (positive-semidefinite Hermitian
powers stay positive-semidefinite): `(ô²)^{2j} = ((ô²)ʲ)ᴴ (ô²)ʲ` and
`(ô²)^{2j+1} = ((ô²)ʲ)ᴴ ô² (ô²)ʲ`. -/
theorem orderSqOp_pow_posSemidef (d L N : ℕ) [NeZero L] (k : ℕ) :
    (orderSqOp (torusParitySublattice d L) N ^ k).PosSemidef := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have := Matrix.posSemidef_conjTranspose_mul_self (orderSqOp (torusParitySublattice d L) N ^ j)
    rwa [((orderSqOp_torus_isHermitian d L N).pow j).eq, ← pow_add, ← hj] at this
  · have h := (orderSqOp_torus_posSemidef d L N).conjTranspose_mul_mul_same
      (orderSqOp (torusParitySublattice d L) N ^ j)
    rwa [((orderSqOp_torus_isHermitian d L N).pow j).eq,
      show orderSqOp (torusParitySublattice d L) N ^ j * orderSqOp (torusParitySublattice d L) N
        * orderSqOp (torusParitySublattice d L) N ^ j
        = orderSqOp (torusParitySublattice d L) N ^ (2 * j + 1) from by
          rw [← pow_succ, ← pow_add]; congr 1; omega, ← hj] at h

/-! ### The `ô²`-moment and its log-convexity -/

/-- The **`ô²`-moment** `R_k := ⟨Φ, (ô²)^k Φ⟩` (real, since `(ô²)^k` is Hermitian). -/
noncomputable def orderSqMoment (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (k : ℕ) : ℝ :=
  (star Φ ⬝ᵥ (orderSqOp (torusParitySublattice d L) N ^ k).mulVec Φ).re

/-- The complex `ô²`-moment equals its (real) `orderSqMoment`. -/
theorem orderSq_dotProduct_eq_orderSqMoment (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (k : ℕ) :
    star Φ ⬝ᵥ (orderSqOp (torusParitySublattice d L) N ^ k).mulVec Φ
      = (orderSqMoment d L N Φ k : ℂ) := by
  rw [orderSqMoment, Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨rfl, hermitian_dotProduct_im_zero ((orderSqOp_torus_isHermitian d L N).pow k) Φ⟩

/-- **The `j`-th `ô²`-tower term has squared `L²` norm `R_{2j}`**: `‖(ô²)ʲ Φ‖² = R_{2j}` (Tasaki
eq. (4.2.60) building block).  Since `ô²` is Hermitian, `⟨(ô²)ʲ Φ, (ô²)ʲ Φ⟩ = ⟨Φ, (ô²)^{2j} Φ⟩`
(`hermitian_pow_dotProduct_split`), whose real part is `orderSqMoment d L N Φ (2 j)`.  Exported for
the sphere-average final assembly (Proposition 4.10, PR-6c), where the normalization denominator of
`(ô²)ʲ Φ` must be read off as the moment `R_{2j}`. -/
theorem vecNormSqRe_orderSqPow_mulVec (d L N j : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    vecNormSqRe ((orderSqOp (torusParitySublattice d L) N ^ j).mulVec Φ)
      = orderSqMoment d L N Φ (2 * j) := by
  rw [vecNormSqRe, hermitian_pow_dotProduct_split (orderSqOp_torus_isHermitian d L N) j j Φ,
    orderSq_dotProduct_eq_orderSqMoment, Complex.ofReal_re, two_mul]

/-- The `ô²`-moments are nonnegative: `R_k ≥ 0`. -/
theorem orderSqMoment_nonneg (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (k : ℕ) :
    0 ≤ orderSqMoment d L N Φ k :=
  (Complex.le_def.mp ((orderSqOp_pow_posSemidef d L N k).dotProduct_mulVec_nonneg Φ)).1

/-- **Log-convexity of the `ô²`-moments** (Cauchy–Schwarz, eq. (4.2.35) for `ô²`):
`R_{n+1}² ≤ R_n · R_{n+2}`.  Even centres use the standard inner product (`M = 1`), odd centres the
`ô²`-weighted form (`M = ô²`); both reduce to the positive-semidefinite Cauchy–Schwarz of the
moments read as `ô²`-power inner products. -/
theorem orderSqMoment_sq_le (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (n : ℕ) :
    (orderSqMoment d L N Φ (n + 1)) ^ 2
      ≤ orderSqMoment d L N Φ n * orderSqMoment d L N Φ (n + 2) := by
  have hH := orderSqOp_torus_isHermitian d L N
  rcases Nat.even_or_odd n with ⟨a, ha⟩ | ⟨a, ha⟩
  · -- `n = a + a` (even centre `n+1`): `M = 1`.
    have hone : (1 : Matrix (HypercubicTorus d L → Fin (N + 1))
        (HypercubicTorus d L → Fin (N + 1)) ℂ).PosSemidef :=
      Matrix.PosSemidef.of_dotProduct_mulVec_nonneg Matrix.isHermitian_one
        (fun x => by rw [Matrix.one_mulVec]; exact dotProduct_star_self_nonneg x)
    have hcs := posSemidef_re_dotProduct_mulVec_sq_le hone
      ((orderSqOp (torusParitySublattice d L) N ^ a).mulVec Φ)
      ((orderSqOp (torusParitySublattice d L) N ^ (a + 1)).mulVec Φ)
    simp only [Matrix.one_mulVec] at hcs
    rw [hermitian_pow_dotProduct_split hH a (a + 1) Φ,
      hermitian_pow_dotProduct_split hH a a Φ,
      hermitian_pow_dotProduct_split hH (a + 1) (a + 1) Φ,
      orderSq_dotProduct_eq_orderSqMoment, orderSq_dotProduct_eq_orderSqMoment,
      orderSq_dotProduct_eq_orderSqMoment, Complex.ofReal_re, Complex.ofReal_re,
      Complex.ofReal_re] at hcs
    subst ha
    convert hcs using 3
    all_goals omega
  · -- `n = 2a+1` (odd centre `n+1`): `M = ô²`.
    have hpm : ∀ k : ℕ, (orderSqOp (torusParitySublattice d L) N).mulVec
        ((orderSqOp (torusParitySublattice d L) N ^ k).mulVec Φ)
        = (orderSqOp (torusParitySublattice d L) N ^ (k + 1)).mulVec Φ :=
      fun k => by rw [Matrix.mulVec_mulVec, ← pow_succ']
    have hcs := posSemidef_re_dotProduct_mulVec_sq_le (orderSqOp_torus_posSemidef d L N)
      ((orderSqOp (torusParitySublattice d L) N ^ a).mulVec Φ)
      ((orderSqOp (torusParitySublattice d L) N ^ (a + 1)).mulVec Φ)
    rw [hpm a, hpm (a + 1), hermitian_pow_dotProduct_split hH a (a + 2) Φ,
      hermitian_pow_dotProduct_split hH a (a + 1) Φ,
      hermitian_pow_dotProduct_split hH (a + 1) (a + 2) Φ,
      orderSq_dotProduct_eq_orderSqMoment, orderSq_dotProduct_eq_orderSqMoment,
      orderSq_dotProduct_eq_orderSqMoment, Complex.ofReal_re, Complex.ofReal_re,
      Complex.ofReal_re] at hcs
    subst ha
    convert hcs using 3
    all_goals omega

/-! ### The base ratio bound and the telescoped lower bound -/

/-- **Base `ô²`-moment ratio bound** `R_1 ≥ q₀ · (L^d)² · R_0` (no isotropy).  Splitting
`ô² = (L^d)² · p̂ + (ô^{(3)})²`, the transverse part `(L^d)² · p̂` is positive-semidefinite and is
dropped; the surviving longitudinal expectation `⟨(ô^{(3)})²⟩` is bounded below by the
long-range-order hypothesis `q₀ ≤ ⟨(ô^{(3)})²⟩ / (‖Φ‖² (L^d)²)`. -/
theorem orderSqMoment_one_ge (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (hΦ : Φ ≠ 0) {q₀ : ℝ}
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)) :
    q₀ * ((L : ℝ) ^ d) ^ 2 * orderSqMoment d L N Φ 0 ≤ orderSqMoment d L N Φ 1 := by
  have hV2Rpos : (0 : ℝ) < ((L : ℝ) ^ d) ^ 2 := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hR0pos : 0 < (star Φ ⬝ᵥ Φ).re :=
    (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  have hM0 : orderSqMoment d L N Φ 0 = (star Φ ⬝ᵥ Φ).re := by
    simp only [orderSqMoment, pow_zero, Matrix.one_mulVec]
  have hP : 0 ≤ (star Φ ⬝ᵥ (staggeredPhatS d L N).mulVec Φ).re :=
    (Complex.le_def.mp ((staggeredPhatS_posSemidef d L N).dotProduct_mulVec_nonneg Φ)).1
  have hsplit : orderSqMoment d L N Φ 1
      = ((L : ℝ) ^ d) ^ 2 * (star Φ ⬝ᵥ (staggeredPhatS d L N).mulVec Φ).re
        + (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
            * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re := by
    simp only [orderSqMoment, pow_one]
    rw [orderSqOp_eq_smul_staggeredPhatS_add_sq,
      show staggeredOrderOpS (torusParitySublattice d L) N ^ 2
        = staggeredOrderOpS (torusParitySublattice d L) N
          * staggeredOrderOpS (torusParitySublattice d L) N from pow_two _,
      Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      Complex.add_re,
      show (((L : ℂ) ^ d) ^ 2) = ((((L : ℝ) ^ d) ^ 2 : ℝ) : ℂ) from by push_cast; ring,
      Complex.re_ofReal_mul]
  have hden : 0 < (star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2 := mul_pos hR0pos hV2Rpos
  have hQ : q₀ * ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)
      ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
          * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re :=
    (le_div_iff₀ hden).mp hlro
  rw [hsplit, hM0]
  nlinarith [hP, hV2Rpos, hQ]

/-- **`ô²`-moment lower bound under long-range order** (PR-4a tip, eqs. (4.2.36)/(4.2.37) for `ô²`):
if `Φ ≠ 0`, `0 ≤ q₀`, and the long-range-order hypothesis
`q₀ ≤ ⟨(ô^{(3)})²⟩ / (‖Φ‖² (L^d)²)` holds, then `R_m ≥ (q₀ · (L^d)²)^m · R_0` for every `m`.
Telescoping of the log-convexity (`orderSqMoment_sq_le`) from the base bound
(`orderSqMoment_one_ge`) via `real_logConvex_geometric_lower`. -/
theorem orderSqMoment_ge (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (hΦ : Φ ≠ 0) {q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)) (m : ℕ) :
    (q₀ * ((L : ℝ) ^ d) ^ 2) ^ m * orderSqMoment d L N Φ 0 ≤ orderSqMoment d L N Φ m := by
  rcases m with _ | n
  · simp
  · have hr : 0 ≤ q₀ * ((L : ℝ) ^ d) ^ 2 := mul_nonneg hq₀ (by positivity)
    have hm0 : 0 < orderSqMoment d L N Φ 0 := by
      rw [show orderSqMoment d L N Φ 0 = (star Φ ⬝ᵥ Φ).re from by
        simp only [orderSqMoment, pow_zero, Matrix.one_mulVec]]
      exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
    exact LatticeSystem.Math.real_logConvex_geometric_lower (orderSqMoment_nonneg d L N Φ)
      (orderSqMoment_sq_le d L N Φ) hr hm0 (orderSqMoment_one_ge d L N Φ hΦ hlro) n

end LatticeSystem.Quantum
