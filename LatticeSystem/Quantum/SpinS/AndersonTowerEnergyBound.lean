import LatticeSystem.Quantum.SpinS.OrderOperatorAlgebra
import LatticeSystem.Quantum.SpinS.CyclicCommutator31
import LatticeSystem.Quantum.SpinS.CyclicCommutator23
import LatticeSystem.Math.PosSemidef.Basics
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Tasaki §4.2.1 Theorem 4.6: Anderson tower energy bound — phat foundations

The Anderson tower energy bound (Theorem 4.6) is proved, *given* the long-range-order hypothesis
`q₀`, as a purely finite-volume variational estimate (no reflection positivity — that only enters in
establishing `q₀ > 0`, which is here a hypothesis).  This file collects the `U(1)`-symmetric
order-operator `p̂ = ½(ô⁺ô⁻ + ô⁻ô⁺)` foundations used throughout: the order-density adjoint relation
`(ô^b)ᴴ = ô^{¬b}`, the Hermiticity of `p̂`, its positive-semidefiniteness `⟨Φ, p̂ Φ⟩ ≥ 0` (since
`p̂ = (ô⁽¹⁾)² + (ô⁽²⁾)²` with `ô⁽¹⁾, ô⁽²⁾` Hermitian), and the Cauchy–Schwarz monotonicity of the
moments `⟨Φ, p̂ⁿ Φ⟩` (eq. (4.2.35)).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1–§4.2.2, Theorem 4.6, eqs. (4.2.3)–(4.2.7), (4.2.35); cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Real Cauchy–Schwarz for a positive-semidefinite matrix form**: for `M` positive-semidefinite
and any vectors `x, y`, `(Re⟨x, M y⟩)² ≤ ⟨x, M x⟩.re · ⟨y, M y⟩.re`, by the nonnegative-discriminant
of the real quadratic `t ↦ ⟨x + t y, M (x + t y)⟩.re ≥ 0`. -/
theorem posSemidef_re_dotProduct_mulVec_sq_le {n : Type*} [Fintype n]
    {M : Matrix n n ℂ} (hM : M.PosSemidef) (x y : n → ℂ) :
    (star x ⬝ᵥ M.mulVec y).re ^ 2
      ≤ (star x ⬝ᵥ M.mulVec x).re * (star y ⬝ᵥ M.mulVec y).re := by
  classical
  -- Hermitian symmetry of the off-diagonal real part.
  have hsymm : (star y ⬝ᵥ M.mulVec x).re = (star x ⬝ᵥ M.mulVec y).re := by
    have h1 : star x ⬝ᵥ M.mulVec y = star (star y ⬝ᵥ M.mulVec x) := by
      rw [Matrix.star_dotProduct, Matrix.star_mulVec, hM.isHermitian.eq, ← dotProduct_mulVec]
    rw [h1, Complex.star_def, Complex.conj_re]
  -- Four-term expansion of the diagonal of `x + t y`.
  have hexp : ∀ t : ℝ, star (x + (t : ℂ) • y) ⬝ᵥ M.mulVec (x + (t : ℂ) • y)
      = star x ⬝ᵥ M.mulVec x + (t : ℂ) * (star x ⬝ᵥ M.mulVec y)
        + (t : ℂ) * (star y ⬝ᵥ M.mulVec x) + (t : ℂ) * (t : ℂ) * (star y ⬝ᵥ M.mulVec y) := by
    intro t
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, star_add, star_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, Complex.star_def, Complex.conj_ofReal,
      smul_eq_mul]
    ring
  -- The quadratic `t ↦ ⟨x+ty, M(x+ty)⟩.re` is nonnegative for all real `t`.
  have hquad : ∀ t : ℝ, 0 ≤ (star y ⬝ᵥ M.mulVec y).re * (t * t)
      + 2 * (star x ⬝ᵥ M.mulVec y).re * t + (star x ⬝ᵥ M.mulVec x).re := by
    intro t
    have hnn := (Complex.le_def.mp (hM.dotProduct_mulVec_nonneg (x + (t : ℂ) • y))).1
    rw [hexp t] at hnn
    simp only [Complex.zero_re, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at hnn
    rw [hsymm] at hnn
    nlinarith [hnn]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- **Single-stage Hermitian shift**: `⟨Φ, (S X) Φ⟩ = ⟨S Φ, X Φ⟩` for Hermitian `S`. -/
theorem hermitian_dotProduct_shift {n : Type*} [Fintype n] {S X : Matrix n n ℂ}
    (hS : S.IsHermitian) (Φ : n → ℂ) :
    star Φ ⬝ᵥ (S * X).mulVec Φ = star (S.mulVec Φ) ⬝ᵥ X.mulVec Φ := by
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec]
  congr 1
  rw [Matrix.star_mulVec, hS.eq]

/-- **Splitting a Hermitian power across a dot product**: for Hermitian `H`,
`⟨HᵃΦ, HᵇΦ⟩ = ⟨Φ, H^{a+b}Φ⟩`.  Lets the moments `⟨Φ, HᵏΦ⟩` be read as inner products of `H`-powers
of `Φ`, the input to the Cauchy–Schwarz moment inequalities. -/
theorem hermitian_pow_dotProduct_split {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (a b : ℕ) (Φ : n → ℂ) :
    star ((H ^ a).mulVec Φ) ⬝ᵥ ((H ^ b).mulVec Φ) = star Φ ⬝ᵥ (H ^ (a + b)).mulVec Φ := by
  rw [Matrix.star_mulVec, ← dotProduct_mulVec, (hH.pow a).eq, Matrix.mulVec_mulVec, ← pow_add]

/-- **Hermitian quadratic forms are real**: `⟨Φ, H Φ⟩.im = 0` for Hermitian `H`. -/
theorem hermitian_dotProduct_im_zero {n : Type*} [Fintype n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (Φ : n → ℂ) : (star Φ ⬝ᵥ H.mulVec Φ).im = 0 := by
  classical
  have h1 : (starRingEnd ℂ) (star Φ ⬝ᵥ H.mulVec Φ) = star Φ ⬝ᵥ H.mulVec Φ := by
    rw [starRingEnd_apply, ← Matrix.star_dotProduct, Matrix.star_mulVec, hH.eq,
      ← dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h1

/-- The **staggered raising order operator is the adjoint of the lowering one**:
`(Ô_L^+)ᴴ = Ô_L^−` (each per-site `Ŝ⁺` adjoints to `Ŝ⁻`, and the staggered signs `±1` are real). -/
theorem staggeredRaisingOpS_conjTranspose (A : Λ → Bool) :
    Matrix.conjTranspose (staggeredRaisingOpS A N) = staggeredLoweringOpS A N := by
  unfold staggeredRaisingOpS staggeredLoweringOpS spinSSiteOpPlus spinSSiteOpMinus
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Matrix.conjTranspose_smul, onSiteS_conjTranspose, spinSOpPlus_conjTranspose]
  congr 1
  split_ifs <;> simp

/-- The **staggered lowering order operator is the adjoint of the raising one**:
`(Ô_L^−)ᴴ = Ô_L^+`. -/
theorem staggeredLoweringOpS_conjTranspose (A : Λ → Bool) :
    Matrix.conjTranspose (staggeredLoweringOpS A N) = staggeredRaisingOpS A N := by
  rw [← staggeredRaisingOpS_conjTranspose, Matrix.conjTranspose_conjTranspose]

/-- The **per-volume order-density adjoint**: `(ô^b)ᴴ = ô^{¬b}` (the `(L^d)⁻¹` factor is real). -/
theorem staggeredOrderDensityOpS_conjTranspose (d L N : ℕ) [NeZero L] (b : Bool) :
    Matrix.conjTranspose (staggeredOrderDensityOpS d L N b)
      = staggeredOrderDensityOpS d L N (!b) := by
  unfold staggeredOrderDensityOpS
  rw [Matrix.conjTranspose_smul, star_inv₀, star_pow, Complex.star_def, Complex.conj_natCast]
  cases b <;>
    simp [staggeredRaisingOpS_conjTranspose, staggeredLoweringOpS_conjTranspose]

/-- `ô⁻` is the conjugate transpose of `ô⁺`. -/
theorem staggeredOrderDensityOpS_false_eq_conjTranspose (d L N : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false
      = Matrix.conjTranspose (staggeredOrderDensityOpS d L N true) :=
  (staggeredOrderDensityOpS_conjTranspose d L N true).symm

/-- **`ô⁺ô⁻` is positive-semidefinite** (`= ô⁺(ô⁺)ᴴ`). -/
theorem staggeredOrderDensity_mul_posSemidef_tf (d L N : ℕ) [NeZero L] :
    (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (staggeredOrderDensityOpS d L N true)
  rwa [← staggeredOrderDensityOpS_false_eq_conjTranspose] at h

/-- **`ô⁻ô⁺` is positive-semidefinite** (`= (ô⁺)ᴴô⁺`). -/
theorem staggeredOrderDensity_mul_posSemidef_ft (d L N : ℕ) [NeZero L] :
    (staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (staggeredOrderDensityOpS d L N true)
  rwa [← staggeredOrderDensityOpS_false_eq_conjTranspose] at h

/-- **`p̂` is Hermitian**: `p̂ = ½(ô⁺(ô⁺)ᴴ + (ô⁺)ᴴô⁺)` with both summands Hermitian squares. -/
theorem staggeredPhatS_isHermitian (d L N : ℕ) [NeZero L] :
    (staggeredPhatS d L N).IsHermitian := by
  unfold staggeredPhatS
  refine (((staggeredOrderDensity_mul_posSemidef_tf d L N).1.add
    (staggeredOrderDensity_mul_posSemidef_ft d L N).1).smul ?_)
  rw [isSelfAdjoint_iff, Complex.star_def, map_inv₀, Complex.conj_ofNat]

/-- The **`p̂`-moment** `⟨Φ, p̂ᵏ Φ⟩` (real, since `p̂ᵏ` is Hermitian). -/
noncomputable def phatMoment (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (k : ℕ) : ℝ :=
  (star Φ ⬝ᵥ (staggeredPhatS d L N ^ k).mulVec Φ).re

/-- The complex `p̂`-moment equals its (real) `phatMoment`. -/
theorem phat_dotProduct_eq_phatMoment (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (k : ℕ) :
    star Φ ⬝ᵥ (staggeredPhatS d L N ^ k).mulVec Φ = (phatMoment d L N Φ k : ℂ) := by
  rw [phatMoment, Complex.ext_iff, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨rfl, hermitian_dotProduct_im_zero ((staggeredPhatS_isHermitian d L N).pow k) Φ⟩

/-- The `p̂`-expectation factors as `⟨Φ, p̂ Φ⟩ = ½(⟨Φ, ô⁺ô⁻ Φ⟩ + ⟨Φ, ô⁻ô⁺ Φ⟩)` (as a complex
number). -/
theorem staggeredPhatS_dotProduct_mulVec_eq (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    star Φ ⬝ᵥ (staggeredPhatS d L N).mulVec Φ
      = (2 : ℂ)⁻¹ * (star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N true
            * staggeredOrderDensityOpS d L N false).mulVec Φ
          + star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false
            * staggeredOrderDensityOpS d L N true).mulVec Φ) := by
  unfold staggeredPhatS
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.add_mulVec, dotProduct_add]

/-- **`p̂` is positive-semidefinite** as a matrix: `0 ≤ ⟨Φ, p̂ Φ⟩` in the complex order for every
`Φ` (it is the `½`-average of the two Hermitian-square expectations). -/
theorem staggeredPhatS_posSemidef (d L N : ℕ) [NeZero L] :
    (staggeredPhatS d L N).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (staggeredPhatS_isHermitian d L N)
    (fun Φ => ?_)
  rw [staggeredPhatS_dotProduct_mulVec_eq]
  have hz1 := (staggeredOrderDensity_mul_posSemidef_tf d L N).dotProduct_mulVec_nonneg Φ
  have hz2 := (staggeredOrderDensity_mul_posSemidef_ft d L N).dotProduct_mulVec_nonneg Φ
  have h2 : (0 : ℂ) ≤ (2 : ℂ)⁻¹ := by
    rw [Complex.le_def]; constructor <;> norm_num
  exact mul_nonneg h2 (add_nonneg hz1 hz2)

/-- The expectation of `p̂` is nonnegative: `⟨Φ, p̂ Φ⟩.re ≥ 0`. -/
theorem staggeredPhatS_expectation_nonneg (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    0 ≤ (star Φ ⬝ᵥ (staggeredPhatS d L N).mulVec Φ).re :=
  (Complex.le_def.mp ((staggeredPhatS_posSemidef d L N).dotProduct_mulVec_nonneg Φ)).1

/-- **`p̂ᵏ` is positive-semidefinite** for every `k` (powers of a positive-semidefinite Hermitian
operator stay positive-semidefinite): `p̂^{2j} = (p̂ʲ)ᴴ p̂ʲ` and `p̂^{2j+1} = (p̂ʲ)ᴴ p̂ p̂ʲ`. -/
theorem staggeredPhatS_pow_posSemidef (d L N : ℕ) [NeZero L] (k : ℕ) :
    (staggeredPhatS d L N ^ k).PosSemidef := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have := Matrix.posSemidef_conjTranspose_mul_self (staggeredPhatS d L N ^ j)
    rwa [((staggeredPhatS_isHermitian d L N).pow j).eq, ← pow_add, ← hj] at this
  · have h := (staggeredPhatS_posSemidef d L N).conjTranspose_mul_mul_same
      (staggeredPhatS d L N ^ j)
    rwa [((staggeredPhatS_isHermitian d L N).pow j).eq,
      show staggeredPhatS d L N ^ j * staggeredPhatS d L N * staggeredPhatS d L N ^ j
        = staggeredPhatS d L N ^ (2 * j + 1) from by
          rw [← pow_succ, ← pow_add]; congr 1; omega, ← hj] at h

/-- The `p̂`-moments are nonnegative: `⟨Φ, p̂ᵏ Φ⟩.re ≥ 0`. -/
theorem phatMoment_nonneg (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (k : ℕ) :
    0 ≤ phatMoment d L N Φ k :=
  (Complex.le_def.mp ((staggeredPhatS_pow_posSemidef d L N k).dotProduct_mulVec_nonneg Φ)).1

/-- **Log-convexity of the `p̂`-moments** (Cauchy–Schwarz, eq. (4.2.35)):
`⟨p̂ⁿ⁺¹⟩² ≤ ⟨p̂ⁿ⟩ · ⟨p̂ⁿ⁺²⟩`.  Even centres use the standard inner product (`M = 1`), odd
centres the `p̂`-weighted form (`M = p̂`); both reduce to the positive-semidefinite Cauchy–Schwarz
of the moments read as `p̂`-power inner products. -/
theorem phatMoment_sq_le (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (n : ℕ) :
    (phatMoment d L N Φ (n + 1)) ^ 2
      ≤ phatMoment d L N Φ n * phatMoment d L N Φ (n + 2) := by
  have hH := staggeredPhatS_isHermitian d L N
  rcases Nat.even_or_odd n with ⟨a, ha⟩ | ⟨a, ha⟩
  · -- `n = a + a` (even centre `n+1`): `M = 1`.
    have hone : (1 : Matrix (HypercubicTorus d L → Fin (N + 1))
        (HypercubicTorus d L → Fin (N + 1)) ℂ).PosSemidef :=
      Matrix.PosSemidef.of_dotProduct_mulVec_nonneg Matrix.isHermitian_one
        (fun x => by rw [Matrix.one_mulVec]; exact dotProduct_star_self_nonneg x)
    have hcs := posSemidef_re_dotProduct_mulVec_sq_le hone
      ((staggeredPhatS d L N ^ a).mulVec Φ) ((staggeredPhatS d L N ^ (a + 1)).mulVec Φ)
    simp only [Matrix.one_mulVec] at hcs
    rw [hermitian_pow_dotProduct_split hH a (a + 1) Φ,
      hermitian_pow_dotProduct_split hH a a Φ,
      hermitian_pow_dotProduct_split hH (a + 1) (a + 1) Φ,
      phat_dotProduct_eq_phatMoment, phat_dotProduct_eq_phatMoment,
      phat_dotProduct_eq_phatMoment, Complex.ofReal_re, Complex.ofReal_re,
      Complex.ofReal_re] at hcs
    subst ha
    convert hcs using 3
    all_goals omega
  · -- `n = 2a+1` (odd centre `n+1`): `M = p̂`.
    have hpm : ∀ k : ℕ, (staggeredPhatS d L N).mulVec ((staggeredPhatS d L N ^ k).mulVec Φ)
        = (staggeredPhatS d L N ^ (k + 1)).mulVec Φ :=
      fun k => by rw [Matrix.mulVec_mulVec, ← pow_succ']
    have hcs := posSemidef_re_dotProduct_mulVec_sq_le (staggeredPhatS_posSemidef d L N)
      ((staggeredPhatS d L N ^ a).mulVec Φ) ((staggeredPhatS d L N ^ (a + 1)).mulVec Φ)
    rw [hpm a, hpm (a + 1), hermitian_pow_dotProduct_split hH a (a + 2) Φ,
      hermitian_pow_dotProduct_split hH a (a + 1) Φ,
      hermitian_pow_dotProduct_split hH (a + 1) (a + 2) Φ,
      phat_dotProduct_eq_phatMoment, phat_dotProduct_eq_phatMoment,
      phat_dotProduct_eq_phatMoment, Complex.ofReal_re, Complex.ofReal_re,
      Complex.ofReal_re] at hcs
    subst ha
    convert hcs using 3
    all_goals omega

/-- **Cross log-convexity** of the `p̂`-moments: `m₁·mₙ ≤ m₀·mₙ₊₁` (the ratio `mₙ₊₁/mₙ` is
increasing).  Pure consequence of `phatMoment_sq_le` + nonnegativity (no LRO). -/
theorem phatMoment_cross (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (n : ℕ) :
    phatMoment d L N Φ 1 * phatMoment d L N Φ n
      ≤ phatMoment d L N Φ 0 * phatMoment d L N Φ (n + 1) := by
  set m := phatMoment d L N Φ with hm
  have hnn : ∀ j, 0 ≤ m j := phatMoment_nonneg d L N Φ
  induction n with
  | zero => exact le_of_eq (mul_comm _ _)
  | succ k ih =>
    have hsq : m (k + 1) ^ 2 ≤ m k * m (k + 2) := phatMoment_sq_le d L N Φ k
    rcases eq_or_lt_of_le (hnn k) with h0 | hpos
    · have hle : m (k + 1) ^ 2 ≤ 0 := by rw [← h0, zero_mul] at hsq; exact hsq
      have hk1 : m (k + 1) = 0 := pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hle (sq_nonneg _))
      rw [hk1, mul_zero]
      exact mul_nonneg (hnn 0) (hnn (k + 1 + 1))
    · have key : m k * (m 1 * m (k + 1)) ≤ m k * (m 0 * m (k + 2)) :=
        calc m k * (m 1 * m (k + 1)) = (m 1 * m k) * m (k + 1) := by ring
          _ ≤ (m 0 * m (k + 1)) * m (k + 1) := mul_le_mul_of_nonneg_right ih (hnn (k + 1))
          _ = m 0 * m (k + 1) ^ 2 := by ring
          _ ≤ m 0 * (m k * m (k + 2)) := mul_le_mul_of_nonneg_left hsq (hnn 0)
          _ = m k * (m 0 * m (k + 2)) := by ring
      exact le_of_mul_le_mul_left key hpos

/-- **Geometric lower bound** for the `p̂`-moments: `m₁^{n+1} ≤ m₀ⁿ · mₙ₊₁` (iterating the cross
log-convexity).  Pure (no LRO). -/
theorem phatMoment_geom_le (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (n : ℕ) :
    phatMoment d L N Φ 1 ^ (n + 1)
      ≤ phatMoment d L N Φ 0 ^ n * phatMoment d L N Φ (n + 1) := by
  set m := phatMoment d L N Φ with hm
  have hnn : ∀ j, 0 ≤ m j := phatMoment_nonneg d L N Φ
  induction n with
  | zero => simp
  | succ k ih =>
    calc m 1 ^ (k + 2) = m 1 ^ (k + 1) * m 1 := by ring
      _ ≤ (m 0 ^ k * m (k + 1)) * m 1 := by
          exact mul_le_mul_of_nonneg_right ih (hnn 1)
      _ = m 0 ^ k * (m 1 * m (k + 1)) := by ring
      _ ≤ m 0 ^ k * (m 0 * m (k + 2)) :=
          mul_le_mul_of_nonneg_left (phatMoment_cross d L N Φ (k + 1)) (pow_nonneg (hnn 0) k)
      _ = m 0 ^ (k + 1) * m (k + 2) := by ring

/-- **`p̂`-moment lower bound under long-range order** (eq. (4.2.37)): if `0 < m₀` and the LRO input
`2q₀·m₀ ≤ m₁` holds (with `0 ≤ q₀`), then `(2q₀)^{n+1}·m₀ ≤ mₙ₊₁` (i.e. the normalized moment
`⟨p̂ⁿ⁺¹⟩ ≥ (2q₀)^{n+1}`). -/
theorem phatMoment_ge_of_lro (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1) (n : ℕ) :
    (2 * q₀) ^ (n + 1) * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ (n + 1) := by
  set m := phatMoment d L N Φ with hm
  have h2q0 : 0 ≤ 2 * q₀ := mul_nonneg (by norm_num) hq₀
  have hgeom := phatMoment_geom_le d L N Φ n
  have hpow : (2 * q₀ * m 0) ^ (n + 1) ≤ m 1 ^ (n + 1) :=
    pow_le_pow_left₀ (mul_nonneg h2q0 hm0.le) hlro (n + 1)
  have hkey : (2 * q₀) ^ (n + 1) * m 0 ^ (n + 1) ≤ m 0 ^ n * m (n + 1) := by
    calc (2 * q₀) ^ (n + 1) * m 0 ^ (n + 1)
          = (2 * q₀ * m 0) ^ (n + 1) := (mul_pow (2 * q₀) (m 0) (n + 1)).symm
      _ ≤ m 1 ^ (n + 1) := hpow
      _ ≤ m 0 ^ n * m (n + 1) := hgeom
  have hfinal : m 0 ^ n * ((2 * q₀) ^ (n + 1) * m 0) ≤ m 0 ^ n * m (n + 1) := by
    calc m 0 ^ n * ((2 * q₀) ^ (n + 1) * m 0)
          = (2 * q₀) ^ (n + 1) * m 0 ^ (n + 1) := by rw [pow_succ]; ring
      _ ≤ m 0 ^ n * m (n + 1) := hkey
  exact le_of_mul_le_mul_left hfinal (pow_pos hm0 n)

/-! ### SU(2) rotation of the staggered order operators (P6) -/

/-- Per-site step of the rotation commutator `[Ŝ³_tot, Ô¹] = i Ô²`: the site-`x` `Ŝ³` commutes with
the staggered `Ô¹` except at its own site, contributing `ε_x · (i Ŝ²_x)`. -/
private theorem spinSSiteOp3_commutator_staggeredOrderOp1S (A : Λ → Bool) (x : Λ) :
    spinSSiteOp3 x N * staggeredOrderOp1S A N - staggeredOrderOp1S A N * spinSSiteOp3 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • (Complex.I • spinSSiteOp2 x N) := by
  unfold staggeredOrderOp1S spinSSiteOp3 spinSSiteOp1 spinSSiteOp2
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub, spinSOp3_commutator_spinSOp1, onSiteS_smul]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp3 N) (spinSOp1 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Rotation commutator** `[Ŝ³_tot, Ô_L^{(1)}] = i Ô_L^{(2)}`: cross-site terms vanish; on-site
terms give the single-site `[Ŝ³, Ŝ¹] = i Ŝ²`. -/
theorem totalSpinSOp3_commutator_staggeredOrderOp1S (A : Λ → Bool) :
    totalSpinSOp3 Λ N * staggeredOrderOp1S A N - staggeredOrderOp1S A N * totalSpinSOp3 Λ N
      = Complex.I • staggeredOrderOp2S A N := by
  have hsum : (totalSpinSOp3 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp3 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, staggeredOrderOp2S,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp3_commutator_staggeredOrderOp1S, smul_comm (if A x then (1 : ℂ) else (-1 : ℂ))]

/-- Per-site step of `[Ŝ³_tot, Ô²] = -i Ô¹`: on-site `[Ŝ³, Ŝ²] = -i Ŝ¹`. -/
private theorem spinSSiteOp3_commutator_staggeredOrderOp2S (A : Λ → Bool) (x : Λ) :
    spinSSiteOp3 x N * staggeredOrderOp2S A N - staggeredOrderOp2S A N * spinSSiteOp3 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • ((-Complex.I) • spinSSiteOp1 x N) := by
  unfold staggeredOrderOp2S spinSSiteOp3 spinSSiteOp2 spinSSiteOp1
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub,
      show spinSOp3 N * spinSOp2 N - spinSOp2 N * spinSOp3 N = (-Complex.I) • spinSOp1 N from by
        rw [← neg_sub, spinSOp2_commutator_spinSOp3, neg_smul], onSiteS_smul]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp3 N) (spinSOp2 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Rotation commutator** `[Ŝ³_tot, Ô_L^{(2)}] = -i Ô_L^{(1)}`. -/
theorem totalSpinSOp3_commutator_staggeredOrderOp2S (A : Λ → Bool) :
    totalSpinSOp3 Λ N * staggeredOrderOp2S A N - staggeredOrderOp2S A N * totalSpinSOp3 Λ N
      = (-Complex.I) • staggeredOrderOp1S A N := by
  have hsum : (totalSpinSOp3 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp3 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, staggeredOrderOp1S,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp3_commutator_staggeredOrderOp2S, smul_comm (if A x then (1 : ℂ) else (-1 : ℂ))]

/-- **Generic singlet component equality**: if `S` is Hermitian with `S Φ = 0` and rotates `A, B`
as `[S, A] = i B`, `[S, B] = −i A`, then `⟨Φ, A² Φ⟩ = ⟨Φ, B² Φ⟩`.  Via `[S, AB] = i(B²−A²)` and the
Hermitian shift killing both sides on the singlet. -/
theorem singlet_sq_expectation_eq {S A B : ManyBodyOpS Λ N} (hS : S.IsHermitian)
    (hcomm1 : S * A - A * S = Complex.I • B) (hcomm2 : S * B - B * S = (-Complex.I) • A)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (hsing : S.mulVec Φ = 0) :
    star Φ ⬝ᵥ (A * A).mulVec Φ = star Φ ⬝ᵥ (B * B).mulVec Φ := by
  have hleib : S * (A * B) - A * B * S = Complex.I • (B * B - A * A) := by
    have e : S * (A * B) - A * B * S
        = (S * A - A * S) * B + A * (S * B - B * S) := by noncomm_ring
    rw [e, hcomm1, hcomm2, smul_mul_assoc, mul_smul_comm, neg_smul, ← sub_eq_add_neg, ← smul_sub]
  have hcomm0 : star Φ ⬝ᵥ (S * (A * B) - A * B * S).mulVec Φ = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, hermitian_dotProduct_shift hS, hsing, star_zero,
      zero_dotProduct, ← Matrix.mulVec_mulVec, hsing, Matrix.mulVec_zero, dotProduct_zero, sub_zero]
  rw [hleib, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hcomm0
  have h2 : star Φ ⬝ᵥ (B * B - A * A).mulVec Φ = 0 :=
    (mul_eq_zero.mp hcomm0).resolve_left Complex.I_ne_zero
  rw [Matrix.sub_mulVec, dotProduct_sub, sub_eq_zero] at h2
  exact h2.symm

/-- **Transverse component equality** (P6, eq. 4.1.7): for a total-`Ŝ³`-singlet state,
`⟨Φ, (Ô¹)² Φ⟩ = ⟨Φ, (Ô²)² Φ⟩`. -/
theorem staggeredOrder_sq_expectation_eq_12 (A : Λ → Bool) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    star Φ ⬝ᵥ (staggeredOrderOp1S A N * staggeredOrderOp1S A N).mulVec Φ
      = star Φ ⬝ᵥ (staggeredOrderOp2S A N * staggeredOrderOp2S A N).mulVec Φ :=
  singlet_sq_expectation_eq (totalSpinSOp3_isHermitian Λ N)
    (totalSpinSOp3_commutator_staggeredOrderOp1S A)
    (totalSpinSOp3_commutator_staggeredOrderOp2S A) Φ hsing

/-- Per-site step of `[Ŝ¹_tot, Ô²] = i Ô³`: on-site `[Ŝ¹, Ŝ²] = i Ŝ³`. -/
private theorem spinSSiteOp1_commutator_staggeredOrderOp2S (A : Λ → Bool) (x : Λ) :
    spinSSiteOp1 x N * staggeredOrderOp2S A N - staggeredOrderOp2S A N * spinSSiteOp1 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • (Complex.I • spinSSiteOp3 x N) := by
  unfold staggeredOrderOp2S spinSSiteOp1 spinSSiteOp2 spinSSiteOp3
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub, spinSOp1_commutator_spinSOp2, onSiteS_smul]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp1 N) (spinSOp2 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Rotation commutator** `[Ŝ¹_tot, Ô_L^{(2)}] = i Ô_L^{(3)}`. -/
theorem totalSpinSOp1_commutator_staggeredOrderOp2S (A : Λ → Bool) :
    totalSpinSOp1 Λ N * staggeredOrderOp2S A N - staggeredOrderOp2S A N * totalSpinSOp1 Λ N
      = Complex.I • staggeredOrderOpS A N := by
  have hsum : (totalSpinSOp1 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp1 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, staggeredOrderOpS,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp1_commutator_staggeredOrderOp2S, smul_comm (if A x then (1 : ℂ) else (-1 : ℂ))]

/-- Per-site step of `[Ŝ¹_tot, Ô³] = -i Ô²`: on-site `[Ŝ¹, Ŝ³] = -i Ŝ²`. -/
private theorem spinSSiteOp1_commutator_staggeredOrderOpS (A : Λ → Bool) (x : Λ) :
    spinSSiteOp1 x N * staggeredOrderOpS A N - staggeredOrderOpS A N * spinSSiteOp1 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • ((-Complex.I) • spinSSiteOp2 x N) := by
  unfold staggeredOrderOpS spinSSiteOp1 spinSSiteOp3 spinSSiteOp2
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub,
      show spinSOp1 N * spinSOp3 N - spinSOp3 N * spinSOp1 N = (-Complex.I) • spinSOp2 N from by
        rw [← neg_sub, spinSOp3_commutator_spinSOp1, neg_smul], onSiteS_smul]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp1 N) (spinSOp3 N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Rotation commutator** `[Ŝ¹_tot, Ô_L^{(3)}] = -i Ô_L^{(2)}`. -/
theorem totalSpinSOp1_commutator_staggeredOrderOpS (A : Λ → Bool) :
    totalSpinSOp1 Λ N * staggeredOrderOpS A N - staggeredOrderOpS A N * totalSpinSOp1 Λ N
      = (-Complex.I) • staggeredOrderOp2S A N := by
  have hsum : (totalSpinSOp1 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp1 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, staggeredOrderOp2S,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp1_commutator_staggeredOrderOpS, smul_comm (if A x then (1 : ℂ) else (-1 : ℂ))]

/-- **Component equality** (P6): for a total-`Ŝ¹`-singlet state,
`⟨Φ, (Ô²)² Φ⟩ = ⟨Φ, (Ô³)² Φ⟩`. -/
theorem staggeredOrder_sq_expectation_eq_23 (A : Λ → Bool) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    star Φ ⬝ᵥ (staggeredOrderOp2S A N * staggeredOrderOp2S A N).mulVec Φ
      = star Φ ⬝ᵥ (staggeredOrderOpS A N * staggeredOrderOpS A N).mulVec Φ :=
  singlet_sq_expectation_eq (totalSpinSOp1_isHermitian Λ N)
    (totalSpinSOp1_commutator_staggeredOrderOp2S A)
    (totalSpinSOp1_commutator_staggeredOrderOpS A) Φ hsing

/-! ### From the LRO premise to `⟨p̂⟩ ≥ 2 q₀` (P7) -/

/-- Cartesian decomposition of the raising operator: `Ŝ⁺ = Ŝ¹ + i Ŝ²`. -/
theorem spinSOpPlus_eq_cartesian (N : ℕ) :
    spinSOpPlus N = spinSOp1 N + Complex.I • spinSOp2 N := by
  unfold spinSOp1 spinSOp2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by
    rw [mul_one_div]; field_simp]
  module

/-- Cartesian decomposition of the lowering operator: `Ŝ⁻ = Ŝ¹ − i Ŝ²`. -/
theorem spinSOpMinus_eq_cartesian (N : ℕ) :
    spinSOpMinus N = spinSOp1 N - Complex.I • spinSOp2 N := by
  unfold spinSOp1 spinSOp2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by
    rw [mul_one_div]; field_simp]
  module

/-- Per-site Cartesian decomposition `Ŝ_x⁺ = Ŝ_x¹ + i Ŝ_x²`. -/
theorem spinSSiteOpPlus_eq_cartesian (x : Λ) :
    spinSSiteOpPlus x N = spinSSiteOp1 x N + Complex.I • spinSSiteOp2 x N := by
  unfold spinSSiteOpPlus spinSSiteOp1 spinSSiteOp2
  rw [spinSOpPlus_eq_cartesian, onSiteS_add, onSiteS_smul]

/-- Per-site Cartesian decomposition `Ŝ_x⁻ = Ŝ_x¹ − i Ŝ_x²`. -/
theorem spinSSiteOpMinus_eq_cartesian (x : Λ) :
    spinSSiteOpMinus x N = spinSSiteOp1 x N - Complex.I • spinSSiteOp2 x N := by
  unfold spinSSiteOpMinus spinSSiteOp1 spinSSiteOp2
  rw [spinSOpMinus_eq_cartesian, onSiteS_sub, onSiteS_smul]

/-- Cartesian decomposition of the staggered raising operator `Ô⁺ = Ô¹ + i Ô²`. -/
theorem staggeredRaisingOpS_eq_cartesian (A : Λ → Bool) :
    staggeredRaisingOpS A N = staggeredOrderOp1S A N + Complex.I • staggeredOrderOp2S A N := by
  unfold staggeredRaisingOpS staggeredOrderOp1S staggeredOrderOp2S
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOpPlus_eq_cartesian, smul_add, smul_comm Complex.I]

/-- Cartesian decomposition of the staggered lowering operator `Ô⁻ = Ô¹ − i Ô²`. -/
theorem staggeredLoweringOpS_eq_cartesian (A : Λ → Bool) :
    staggeredLoweringOpS A N = staggeredOrderOp1S A N - Complex.I • staggeredOrderOp2S A N := by
  unfold staggeredLoweringOpS staggeredOrderOp1S staggeredOrderOp2S
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOpMinus_eq_cartesian, smul_sub, smul_comm Complex.I]

/-- Algebraic expansion `(A + iB)(A − iB) + (A − iB)(A + iB) = 2(A² + B²)` (the imaginary cross
terms cancel; `i² = −1`). -/
theorem cartesian_ladder_anticomm_expand {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) :
    (A + Complex.I • B) * (A - Complex.I • B) + (A - Complex.I • B) * (A + Complex.I • B)
      = (2 : ℂ) • (A * A + B * B) := by
  have hI : (Complex.I • B) * (Complex.I • B) = -(B * B) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [add_mul, sub_mul, mul_sub, mul_sub, mul_add, mul_add, hI]
  module

/-- **`U(1)` order operator as transverse square sum** `p̂ = V⁻² (Ô¹² + Ô²²)` (eq. (4.2.31)). -/
theorem staggeredPhatS_eq_cartesian_sq (d L N : ℕ) [NeZero L] :
    staggeredPhatS d L N = (((L : ℂ) ^ d) ^ 2)⁻¹ •
      (staggeredOrderOp1S (torusParitySublattice d L) N
          * staggeredOrderOp1S (torusParitySublattice d L) N
        + staggeredOrderOp2S (torusParitySublattice d L) N
          * staggeredOrderOp2S (torusParitySublattice d L) N) := by
  rw [staggeredPhatS,
    show staggeredOrderDensityOpS d L N true
        = ((L : ℂ) ^ d)⁻¹ • staggeredRaisingOpS (torusParitySublattice d L) N from rfl,
    show staggeredOrderDensityOpS d L N false
        = ((L : ℂ) ^ d)⁻¹ • staggeredLoweringOpS (torusParitySublattice d L) N from rfl,
    staggeredRaisingOpS_eq_cartesian, staggeredLoweringOpS_eq_cartesian,
    smul_mul_smul_comm, smul_mul_smul_comm, ← smul_add, cartesian_ladder_anticomm_expand,
    smul_smul, smul_smul]
  congr 1
  ring

/-- The `p̂`-expectation in Cartesian form: `⟨Φ, p̂ Φ⟩ = V⁻² (⟨Ô¹² ⟩ + ⟨Ô²²⟩)`. -/
theorem staggeredPhatS_dotProduct_cartesian (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    star Φ ⬝ᵥ (staggeredPhatS d L N).mulVec Φ
      = (((L : ℂ) ^ d) ^ 2)⁻¹ *
          (star Φ ⬝ᵥ (staggeredOrderOp1S (torusParitySublattice d L) N
              * staggeredOrderOp1S (torusParitySublattice d L) N).mulVec Φ
            + star Φ ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
              * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec Φ) := by
  rw [staggeredPhatS_eq_cartesian_sq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Matrix.add_mulVec, dotProduct_add]

/-- **P7 (eq. 4.1.7 → LRO bound):** for an `Ŝ³`- and `Ŝ¹`-singlet ground state with squared
staggered order parameter `≥ q₀`, the first `p̂`-moment obeys `2 q₀ ‖Φ‖² ≤ ⟨Φ, p̂ Φ⟩`.  By `SU(2)`
invariance
the three Cartesian order parameters are equal, so `⟨p̂⟩ = 2 ⟨(Ô³/V)²⟩ ≥ 2 q₀ ‖Φ‖²`. -/
theorem phatMoment_one_ge_of_lro (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hsing1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0)
    (q₀ : ℝ) (hm0 : 0 < (star Φ ⬝ᵥ Φ).re) (hL : (0 : ℝ) < (L : ℝ) ^ d)
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)) :
    2 * q₀ * (star Φ ⬝ᵥ Φ).re ≤ phatMoment d L N Φ 1 := by
  set V2 : ℝ := ((L : ℝ) ^ d) ^ 2 with hV2def
  have hV2 : 0 < V2 := pow_pos hL 2
  have hz12 := staggeredOrder_sq_expectation_eq_12 (torusParitySublattice d L) Φ hsing3
  have hz23 := staggeredOrder_sq_expectation_eq_23 (torusParitySublattice d L) Φ hsing1
  -- m₁ = V⁻² (⟨Ô¹²⟩.re + ⟨Ô²²⟩.re) = 2 V⁻² ⟨Ô³²⟩.re
  have hcast : (((L : ℂ) ^ d) ^ 2)⁻¹ = ((V2⁻¹ : ℝ) : ℂ) := by
    rw [hV2def]; push_cast; ring
  have hm1 : phatMoment d L N Φ 1
      = V2⁻¹ * ((star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
          * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        + (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
          * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re) := by
    rw [phatMoment, pow_one, staggeredPhatS_dotProduct_cartesian, hcast, hz12, hz23]
    simp [Complex.mul_re, Complex.add_re]
  rw [hm1]
  -- from LRO: q₀ * (m₀ * V2) ≤ ⟨Ô³²⟩.re
  rw [le_div_iff₀ (mul_pos hm0 hV2)] at hlro
  have hz3 : q₀ * ((star Φ ⬝ᵥ Φ).re * V2)
      ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re := hlro
  rw [← two_mul]
  -- 2 q₀ m₀ ≤ V⁻² · 2 · ⟨Ô³²⟩.re
  have key : 2 * q₀ * (star Φ ⬝ᵥ Φ).re
      = V2⁻¹ * (2 * (q₀ * ((star Φ ⬝ᵥ Φ).re * V2))) := by
    field_simp
  rw [key]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hV2))
  exact mul_le_mul_of_nonneg_left hz3 (by norm_num)

/-- The zeroth `p̂`-moment is the squared norm: `m₀ = ‖Φ‖²`. -/
theorem phatMoment_zero (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    phatMoment d L N Φ 0 = (star Φ ⬝ᵥ Φ).re := by
  rw [phatMoment, pow_zero, Matrix.one_mulVec]

/-- **Renormalized moment ratio** `2 q₀ mₙ ≤ mₙ₊₁` (the engine of Lemma R1): combining the
log-convexity cross inequality `m₁ mₙ ≤ m₀ mₙ₊₁` with the LRO entry `2 q₀ m₀ ≤ m₁` and cancelling
`m₀ > 0`.  Iterating recovers `(2 q₀)ⁿ m₀ ≤ mₙ`. -/
theorem phatMoment_succ_two_q0_le (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hsing1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0)
    (q₀ : ℝ) (hm0 : 0 < (star Φ ⬝ᵥ Φ).re) (hL : (0 : ℝ) < (L : ℝ) ^ d)
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)) (n : ℕ) :
    2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1) := by
  have hP7 : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1 := by
    rw [phatMoment_zero]; exact phatMoment_one_ge_of_lro d L N Φ hsing3 hsing1 q₀ hm0 hL hlro
  have hcross := phatMoment_cross d L N Φ n
  have hm0' : 0 < phatMoment d L N Φ 0 := by rw [phatMoment_zero]; exact hm0
  have hmn : 0 ≤ phatMoment d L N Φ n := phatMoment_nonneg d L N Φ n
  have hkey : phatMoment d L N Φ 0 * (2 * q₀ * phatMoment d L N Φ n)
      ≤ phatMoment d L N Φ 0 * phatMoment d L N Φ (n + 1) :=
    calc phatMoment d L N Φ 0 * (2 * q₀ * phatMoment d L N Φ n)
        = (2 * q₀ * phatMoment d L N Φ 0) * phatMoment d L N Φ n := by ring
      _ ≤ phatMoment d L N Φ 1 * phatMoment d L N Φ n :=
          mul_le_mul_of_nonneg_right hP7 hmn
      _ ≤ phatMoment d L N Φ 0 * phatMoment d L N Φ (n + 1) := hcross
  exact le_of_mul_le_mul_left hkey hm0'

/-! ### Sector commutators `[Ŝ³_tot, Ô^±] = ±Ô^±` (P8-1) -/

/-- Per-site step of `[Ŝ³_tot, Ô⁺] = Ô⁺`: on-site Cartan relation `[Ŝ³, Ŝ⁺] = Ŝ⁺`. -/
private theorem spinSSiteOp3_commutator_staggeredRaisingOpS (A : Λ → Bool) (x : Λ) :
    spinSSiteOp3 x N * staggeredRaisingOpS A N - staggeredRaisingOpS A N * spinSSiteOp3 x N
      = (if A x then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpPlus x N := by
  unfold staggeredRaisingOpS spinSSiteOp3 spinSSiteOpPlus
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub, spinSOp3_commutator_spinSOpPlus]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp3 N) (spinSOpPlus N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Sector commutator** `[Ŝ³_tot, Ô_L⁺] = Ô_L⁺` (the raising order operator increases the total
magnetization by one). -/
theorem totalSpinSOp3_commutator_staggeredRaisingOpS (A : Λ → Bool) :
    totalSpinSOp3 Λ N * staggeredRaisingOpS A N - staggeredRaisingOpS A N * totalSpinSOp3 Λ N
      = staggeredRaisingOpS A N := by
  have hsum : (totalSpinSOp3 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp3 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  conv_rhs => rw [staggeredRaisingOpS]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp3_commutator_staggeredRaisingOpS]

/-- Per-site step of `[Ŝ³_tot, Ô⁻] = −Ô⁻`: on-site Cartan relation `[Ŝ³, Ŝ⁻] = −Ŝ⁻`. -/
private theorem spinSSiteOp3_commutator_staggeredLoweringOpS (A : Λ → Bool) (x : Λ) :
    spinSSiteOp3 x N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * spinSSiteOp3 x N
      = -((if A x then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpMinus x N) := by
  unfold staggeredLoweringOpS spinSSiteOp3 spinSSiteOpMinus
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_eq_single x]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, onSiteS_mul_onSiteS_same,
      onSiteS_mul_onSiteS_same, ← onSiteS_sub, spinSOp3_commutator_spinSOpMinus, onSiteS_neg,
      smul_neg]
  · intro y _ hyx
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub,
      (onSiteS_commute_of_ne (Ne.symm hyx) (spinSOp3 N) (spinSOpMinus N)).eq, sub_self, smul_zero]
  · intro h; exact absurd (Finset.mem_univ x) h

/-- **Sector commutator** `[Ŝ³_tot, Ô_L⁻] = −Ô_L⁻` (the lowering order operator decreases the total
magnetization by one). -/
theorem totalSpinSOp3_commutator_staggeredLoweringOpS (A : Λ → Bool) :
    totalSpinSOp3 Λ N * staggeredLoweringOpS A N - staggeredLoweringOpS A N * totalSpinSOp3 Λ N
      = -staggeredLoweringOpS A N := by
  have hsum : (totalSpinSOp3 Λ N : ManyBodyOpS Λ N) = ∑ x : Λ, spinSSiteOp3 x N := rfl
  rw [hsum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  conv_rhs => rw [staggeredLoweringOpS, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [spinSSiteOp3_commutator_staggeredLoweringOpS]

/-! ### Word sector eigenvalue (P8-2) -/

/-- **Per-volume sector commutator** `[Ŝ³_tot, ô^b] = ε_b ô^b` (`ε_true = +1`, `ε_false = −1`):
the per-volume raising/lowering density shifts the total magnetization by `±1`. -/
theorem totalSpinSOp3_commutator_orderDensity (d L N : ℕ) [NeZero L] (b : Bool) :
    totalSpinSOp3 (HypercubicTorus d L) N * staggeredOrderDensityOpS d L N b
        - staggeredOrderDensityOpS d L N b * totalSpinSOp3 (HypercubicTorus d L) N
      = (if b then (1 : ℂ) else (-1 : ℂ)) • staggeredOrderDensityOpS d L N b := by
  cases b
  · rw [show staggeredOrderDensityOpS d L N false
        = ((L : ℂ) ^ d)⁻¹ • staggeredLoweringOpS (torusParitySublattice d L) N from rfl]
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, totalSpinSOp3_commutator_staggeredLoweringOpS]
    simp [smul_neg]
  · rw [show staggeredOrderDensityOpS d L N true
        = ((L : ℂ) ^ d)⁻¹ • staggeredRaisingOpS (torusParitySublattice d L) N from rfl]
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, totalSpinSOp3_commutator_staggeredRaisingOpS]
    simp

/-- **Single-step magnetization shift**: if `Ŝ³_tot v = λ v` then `Ŝ³_tot (ô^b v) = (λ+ε_b)(ô^b v)`
(`ε_true = +1`, `ε_false = −1`). -/
theorem totalSpinSOp3_mulVec_orderDensity_eigenvec (d L N : ℕ) [NeZero L] (b : Bool)
    {v : (HypercubicTorus d L → Fin (N + 1)) → ℂ} {lam : ℂ}
    (hv : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec v = lam • v) :
    (totalSpinSOp3 (HypercubicTorus d L) N).mulVec
        ((staggeredOrderDensityOpS d L N b).mulVec v)
      = (lam + (if b then (1 : ℂ) else (-1 : ℂ)))
          • (staggeredOrderDensityOpS d L N b).mulVec v := by
  have hcomm := totalSpinSOp3_commutator_orderDensity d L N b
  have key : totalSpinSOp3 (HypercubicTorus d L) N * staggeredOrderDensityOpS d L N b
      = staggeredOrderDensityOpS d L N b * totalSpinSOp3 (HypercubicTorus d L) N
        + (if b then (1 : ℂ) else (-1 : ℂ)) • staggeredOrderDensityOpS d L N b := by
    rw [← hcomm]; abel
  rw [Matrix.mulVec_mulVec, key, Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, add_smul]

/-- The **net magnetization charge** `m(w) = #{true} − #{false}` of an order word `w` (each `ô⁺`
contributes `+1`, each `ô⁻` contributes `−1`), as the sum of per-letter signs. -/
def mCharge (w : List Bool) : ℂ := (w.map (fun b => if b then (1 : ℂ) else (-1 : ℂ))).sum

@[simp] theorem mCharge_nil : mCharge [] = 0 := by simp [mCharge]

theorem mCharge_cons (b : Bool) (w : List Bool) :
    mCharge (b :: w) = (if b then (1 : ℂ) else (-1 : ℂ)) + mCharge w := by
  rw [mCharge, List.map_cons, List.sum_cons, mCharge]

/-- The net charge is real-valued: `(m(w)).im = 0`. -/
@[simp] theorem mCharge_im (w : List Bool) : (mCharge w).im = 0 := by
  induction w with
  | nil => simp
  | cons b w ih => rw [mCharge_cons, Complex.add_im, ih, add_zero]; split_ifs <;> simp

/-- Cons recursion for the ordered word product: `ô^{b::w} = ô^b · ô^{w}`. -/
theorem orderWordProd_cons (d L N : ℕ) [NeZero L] (b : Bool) (w : List Bool) :
    orderWordProd d L N (b :: w)
      = staggeredOrderDensityOpS d L N b * orderWordProd d L N w := by
  rw [orderWordProd, orderWordProd, List.map_cons, List.prod_cons]

/-- Append recursion for the ordered word product: `ô^{w ++ w'} = ô^{w} · ô^{w'}`. -/
theorem orderWordProd_append (d L N : ℕ) [NeZero L] (w w' : List Bool) :
    orderWordProd d L N (w ++ w')
      = orderWordProd d L N w * orderWordProd d L N w' := by
  rw [orderWordProd, orderWordProd, orderWordProd, List.map_append, List.prod_append]

/-- **Word sector eigenvalue**: for a total-`Ŝ³` singlet `v` (`Ŝ³_tot v = 0`), the ordered word
product is an eigenvector `Ŝ³_tot (ô^{w} v) = m(w) (ô^{w} v)` with eigenvalue the net charge. -/
theorem totalSpinSOp3_mulVec_orderWordProd_eigenvec (d L N : ℕ) [NeZero L] (w : List Bool)
    {v : (HypercubicTorus d L → Fin (N + 1)) → ℂ}
    (hv : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec v = 0) :
    (totalSpinSOp3 (HypercubicTorus d L) N).mulVec ((orderWordProd d L N w).mulVec v)
      = mCharge w • (orderWordProd d L N w).mulVec v := by
  induction w with
  | nil =>
    rw [orderWordProd, List.map_nil, List.prod_nil, Matrix.one_mulVec, mCharge_nil, zero_smul, hv]
  | cons b w ih =>
    rw [orderWordProd_cons, ← Matrix.mulVec_mulVec,
      totalSpinSOp3_mulVec_orderDensity_eigenvec d L N b ih]
    congr 1
    rw [mCharge_cons]; ring

/-! ### Generic pieces for the R1 induction (P8-3) -/

/-- The `p̂`-moments are strictly positive under the LRO entry: `0 < mₙ`. -/
theorem phatMoment_pos_of_lro (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {q₀ : ℝ} (hq0 : 0 < q₀)
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1) (n : ℕ) :
    0 < phatMoment d L N Φ n := by
  cases n with
  | zero => exact hm0
  | succ k =>
    have h := phatMoment_ge_of_lro d L N Φ hq0.le hm0 hlro k
    have hpos : 0 < (2 * q₀) ^ (k + 1) * phatMoment d L N Φ 0 :=
      mul_pos (pow_pos (mul_pos (by norm_num) hq0) (k + 1)) hm0
    exact lt_of_lt_of_le hpos h

/-- **Per-volume commutator as a scalar multiple of total spin** `[ô⁺, ô⁻] = (2/V²) Ŝ³_tot`. -/
theorem staggeredOrderDensity_commutator_eq (d L N : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
        - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true
      = (((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹)
          • ((2 : ℂ) • totalSpinSOp3 (HypercubicTorus d L) N) := by
  rw [show staggeredOrderDensityOpS d L N true
        = ((L : ℂ) ^ d)⁻¹ • staggeredRaisingOpS (torusParitySublattice d L) N from rfl,
    show staggeredOrderDensityOpS d L N false
        = ((L : ℂ) ^ d)⁻¹ • staggeredLoweringOpS (torusParitySublattice d L) N from rfl,
    smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, staggeredOrder_commutator]

/-- The net charge has modulus at most the word length: `‖m(w)‖ ≤ |w|` (sum of `±1`s). -/
theorem mCharge_norm_le (w : List Bool) : ‖mCharge w‖ ≤ (w.length : ℝ) := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [mCharge_cons, List.length_cons]
    calc ‖(if b then (1 : ℂ) else (-1 : ℂ)) + mCharge w‖
        ≤ ‖(if b then (1 : ℂ) else (-1 : ℂ))‖ + ‖mCharge w‖ := norm_add_le _ _
      _ ≤ 1 + (w.length : ℝ) := by
          gcongr
          · split_ifs <;> simp
      _ = ((w.length + 1 : ℕ) : ℝ) := by push_cast; ring

/-- **Single-swap factorization** of the order-word product difference:
`ô^{pre++a::b::suf} − ô^{pre++b::a::suf} = ô^{pre} [ô^a, ô^b] ô^{suf}`. -/
theorem orderWordProd_swap_diff_eq (d L N : ℕ) [NeZero L] (pre suf : List Bool) (a b : Bool) :
    orderWordProd d L N (pre ++ a :: b :: suf) - orderWordProd d L N (pre ++ b :: a :: suf)
      = orderWordProd d L N pre
        * (staggeredOrderDensityOpS d L N a * staggeredOrderDensityOpS d L N b
            - staggeredOrderDensityOpS d L N b * staggeredOrderDensityOpS d L N a)
        * orderWordProd d L N suf := by
  have hexp : ∀ x y : Bool, orderWordProd d L N (pre ++ x :: y :: suf)
      = orderWordProd d L N pre
        * (staggeredOrderDensityOpS d L N x * staggeredOrderDensityOpS d L N y)
        * orderWordProd d L N suf := by
    intro x y
    simp only [orderWordProd, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    noncomm_ring
  rw [hexp, hexp, ← sub_mul, ← mul_sub]

/-- **Convex-combination deviation**: if `c · |s| = 1` and every term `f i` lies within `D` of `x`,
then `x` lies within `D` of the uniform average `c · ∑ f`. -/
theorem abs_sub_smul_sum_le {ι : Type*} (s : Finset ι) (c : ℝ) (hc : 0 ≤ c)
    (x : ℝ) (f : ι → ℝ) (D : ℝ) (hcard : c * (s.card : ℝ) = 1)
    (hbound : ∀ i ∈ s, |x - f i| ≤ D) :
    |x - c * ∑ i ∈ s, f i| ≤ D := by
  have hx : x = c * ∑ _i ∈ s, x := by
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hcard, one_mul]
  have hstep : x - c * ∑ i ∈ s, f i = c * ∑ i ∈ s, (x - f i) := by
    rw [Finset.sum_sub_distrib, mul_sub, ← hx]
  rw [hstep, abs_mul, abs_of_nonneg hc]
  calc c * |∑ i ∈ s, (x - f i)|
      ≤ c * ∑ i ∈ s, |x - f i| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ c * ∑ _i ∈ s, D := by gcongr with i hi; exact hbound i hi
    _ = D := by rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, hcard, one_mul]

/-- **Eigenvalue modulus is bounded by the operator norm**: if `B v = λ v` for `v ≠ 0`, then
`‖λ‖ ≤ ‖B‖`.  This is the uniform `|λ_suf| ≤ N/V` engine for the renormalized R1 estimate. -/
theorem eigenvalue_norm_le_manyBodyOperatorNormS {B : ManyBodyOpS Λ N} {lam : ℂ}
    {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ≠ 0) (h : B.mulVec v = lam • v) :
    ‖lam‖ ≤ manyBodyOperatorNormS B := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM]
  set x : EuclideanSpace ℂ (Λ → Fin (N + 1)) := WithLp.toLp 2 v with hxdef
  have hxne : x ≠ 0 := by
    intro hc
    apply hv
    have := congrArg WithLp.ofLp hc
    simpa [hxdef] using this
  have happ : Matrix.toEuclideanCLM (𝕜 := ℂ) B x = lam • x := by
    rw [hxdef, Matrix.toEuclideanCLM_toLp, h, WithLp.toLp_smul]
  have h1 := (Matrix.toEuclideanCLM (𝕜 := ℂ) B).le_opNorm x
  rw [happ, norm_smul] at h1
  exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hxne)

/-! ### Expectation telescoping of swaps (P8-4) -/

/-- The order-density commutator for any pair `a, b` is a scalar multiple of `Ŝ³_tot`:
`ô^a ô^b − ô^b ô^a = σ(a,b) (2/V²) Ŝ³_tot`, `σ = 0` if `a = b`, `±1` otherwise. -/
theorem orderDensity_comm_ab (d L N : ℕ) [NeZero L] (a b : Bool) :
    staggeredOrderDensityOpS d L N a * staggeredOrderDensityOpS d L N b
        - staggeredOrderDensityOpS d L N b * staggeredOrderDensityOpS d L N a
      = (if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))
          • ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹)
              • ((2 : ℂ) • totalSpinSOp3 (HypercubicTorus d L) N)) := by
  rcases a with _ | _ <;> rcases b with _ | _
  · simp
  · rw [← staggeredOrderDensity_commutator_eq]; norm_num
  · rw [show staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
          - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true
        = -(staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true
          - staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false) from by
        rw [neg_sub], ← staggeredOrderDensity_commutator_eq]
    norm_num
  · simp

/-- **Single-swap expectation difference**: for a singlet `Φ`, the expectation of an order word
changes under one adjacent transposition by a real scalar (`σ(a,b) · 2 m(suf)/V²`) times the
expectation of the shortened (charge-removed) word. -/
theorem orderWordProd_swap_dotProduct_eq (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (pre suf : List Bool) (a b : Bool) :
    (star Φ ⬝ᵥ (orderWordProd d L N (pre ++ a :: b :: suf)).mulVec Φ)
        - (star Φ ⬝ᵥ (orderWordProd d L N (pre ++ b :: a :: suf)).mulVec Φ)
      = ((if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))
            * ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf)))
          * (star Φ ⬝ᵥ (orderWordProd d L N (pre ++ suf)).mulVec Φ) := by
  have heig : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec ((orderWordProd d L N suf).mulVec Φ)
      = mCharge suf • (orderWordProd d L N suf).mulVec Φ :=
    totalSpinSOp3_mulVec_orderWordProd_eigenvec d L N suf hsing
  have hvec : (orderWordProd d L N (pre ++ a :: b :: suf)
        - orderWordProd d L N (pre ++ b :: a :: suf)).mulVec Φ
      = ((if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))
            * ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf)))
          • (orderWordProd d L N (pre ++ suf)).mulVec Φ := by
    rw [orderWordProd_swap_diff_eq, orderDensity_comm_ab, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, heig,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, ← orderWordProd_append, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [← dotProduct_sub, ← Matrix.sub_mulVec, hvec, dotProduct_smul, smul_eq_mul]

/-- The order-density commutator acts on a word vector as the scalar `(2/V²) m(suf)`. -/
theorem orderCommutator_mulVec_orderWordProd (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) (suf : List Bool) :
    (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
        - staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true).mulVec
        ((orderWordProd d L N suf).mulVec Φ)
      = ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf))
          • (orderWordProd d L N suf).mulVec Φ := by
  rw [staggeredOrderDensity_commutator_eq, Matrix.smul_mulVec, Matrix.smul_mulVec,
    totalSpinSOp3_mulVec_orderWordProd_eigenvec d L N suf hsing, smul_smul, smul_smul]
  congr 1
  ring

/-- **Single-swap real-expectation bound**: one adjacent transposition changes the real part of the
order-word expectation by at most `(N/V)` times the shortened word's real expectation. -/
theorem orderWordProd_swap_re_diff_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (pre suf : List Bool) (a b : Bool) :
    |(star Φ ⬝ᵥ (orderWordProd d L N (pre ++ a :: b :: suf)).mulVec Φ).re
        - (star Φ ⬝ᵥ (orderWordProd d L N (pre ++ b :: a :: suf)).mulVec Φ).re|
      ≤ (N : ℝ) / (L : ℝ) ^ d
          * |(star Φ ⬝ᵥ (orderWordProd d L N (pre ++ suf)).mulVec Φ).re| := by
  rw [← Complex.sub_re, orderWordProd_swap_dotProduct_eq d L N Φ hsing pre suf a b]
  set κ := (if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))
      * ((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf)) with hκ
  have hLim : ((((L : ℂ) ^ d)⁻¹).im) = 0 := by
    rw [show ((L : ℂ) ^ d)⁻¹ = (((((L : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) from by push_cast; ring]
    exact Complex.ofReal_im _
  have hκim : κ.im = 0 := by
    rw [hκ]
    simp only [Complex.mul_im, Complex.mul_re, mCharge_im, hLim]
    split_ifs <;> simp
  rw [Complex.mul_re, hκim, zero_mul, sub_zero, abs_mul]
  by_cases hu : (orderWordProd d L N suf).mulVec Φ = 0
  · have hz0 : star Φ ⬝ᵥ (orderWordProd d L N (pre ++ suf)).mulVec Φ = 0 := by
      rw [orderWordProd_append, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero, dotProduct_zero]
    rw [hz0]; simp
  · refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have hknorm : ‖((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf))‖
        ≤ (N : ℝ) / (L : ℝ) ^ d :=
      le_trans (eigenvalue_norm_le_manyBodyOperatorNormS hu
          (orderCommutator_mulVec_orderWordProd d L N Φ hsing suf))
        (staggeredOrderDensity_commutator_manyBodyOperatorNormS_le d L N hN)
    have hσ : ‖(if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))‖ ≤ 1 := by
      split_ifs <;> simp
    have hκeq : κ = (κ.re : ℂ) := Complex.ext rfl (by rw [hκim, Complex.ofReal_im])
    calc |κ.re| = ‖(κ.re : ℂ)‖ := (Complex.norm_real _).symm
      _ = ‖κ‖ := by rw [← hκeq]
      _ = ‖(if a = b then (0 : ℂ) else if a then (1 : ℂ) else (-1 : ℂ))‖
            * ‖((((L : ℂ) ^ d)⁻¹ * ((L : ℂ) ^ d)⁻¹) * (2 * mCharge suf))‖ := by
          rw [hκ, norm_mul]
      _ ≤ 1 * ((N : ℝ) / (L : ℝ) ^ d) := by
          apply mul_le_mul hσ hknorm (norm_nonneg _) (by norm_num)
      _ = (N : ℝ) / (L : ℝ) ^ d := one_mul _

/-! ### Swap-chain telescoping and the R1 induction (P8-5) -/

/-- An adjacent transposition preserves each letter count. -/
theorem AdjSwap.count_eq {w w' : List Bool} (h : AdjSwap w w') (c : Bool) :
    w.count c = w'.count c := by
  obtain ⟨pre, suf, a, b, rfl, rfl⟩ := h
  simp only [List.count_append, List.count_cons]
  ring

/-- **Per-swap real-expectation bound for balanced words**: for a balanced length-`2n` word `w`, one
adjacent transposition changes `Re b_w` by at most `(N/V)·B`, where `B` bounds the real expectations
of balanced length-`2(n−1)` words. -/
theorem adjSwap_re_diff_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbnd : ∀ u : List Bool, u.count true = n - 1 → u.count false = n - 1 →
        |(star Φ ⬝ᵥ (orderWordProd d L N u).mulVec Φ).re| ≤ B)
    {w w' : List Bool} (h : AdjSwap w w') (hwt : w.count true = n) (hwf : w.count false = n) :
    |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re
        - (star Φ ⬝ᵥ (orderWordProd d L N w').mulVec Φ).re|
      ≤ (N : ℝ) / (L : ℝ) ^ d * B := by
  obtain ⟨pre, suf, a, b, rfl, rfl⟩ := h
  rcases a with _ | _ <;> rcases b with _ | _
  · -- (false, false): w = w'
    simp only [sub_self, abs_zero]; positivity
  · -- (false, true)
    refine le_trans (orderWordProd_swap_re_diff_le d L N hN Φ hsing pre suf false true) ?_
    refine mul_le_mul_of_nonneg_left (hbnd _ ?_ ?_) (by positivity)
    · simp at hwt ⊢; omega
    · simp at hwf ⊢; omega
  · -- (true, false)
    refine le_trans (orderWordProd_swap_re_diff_le d L N hN Φ hsing pre suf true false) ?_
    refine mul_le_mul_of_nonneg_left (hbnd _ ?_ ?_) (by positivity)
    · simp at hwt ⊢; omega
    · simp at hwf ⊢; omega
  · -- (true, true): w = w'
    simp only [sub_self, abs_zero]; positivity

/-- **Swap-chain telescoping**: a length-`k` swap chain between balanced length-`2n` words changes
`Re b` by at most `k·(N/V)·B`. -/
theorem swapChain_re_diff_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbnd : ∀ u : List Bool, u.count true = n - 1 → u.count false = n - 1 →
        |(star Φ ⬝ᵥ (orderWordProd d L N u).mulVec Φ).re| ≤ B)
    {k : ℕ} {w w' : List Bool} (hc : SwapChain k w w') :
    w.count true = n → w.count false = n →
    |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re
        - (star Φ ⬝ᵥ (orderWordProd d L N w').mulVec Φ).re|
      ≤ (k : ℝ) * ((N : ℝ) / (L : ℝ) ^ d * B) := by
  induction hc with
  | refl w => intro _ _; simp
  | @step j w w' w'' hs hchain ih =>
    intro hwt hwf
    have hw't : w'.count true = n := by rw [← hs.count_eq true]; exact hwt
    have hw'f : w'.count false = n := by rw [← hs.count_eq false]; exact hwf
    have h1 := adjSwap_re_diff_le d L N hN Φ hsing n B hB hbnd hs hwt hwf
    have ih' := ih hw't hw'f
    calc |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re
            - (star Φ ⬝ᵥ (orderWordProd d L N w'').mulVec Φ).re|
        ≤ |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re
              - (star Φ ⬝ᵥ (orderWordProd d L N w').mulVec Φ).re|
          + |(star Φ ⬝ᵥ (orderWordProd d L N w').mulVec Φ).re
              - (star Φ ⬝ᵥ (orderWordProd d L N w'').mulVec Φ).re| := abs_sub_le _ _ _
      _ ≤ (N : ℝ) / (L : ℝ) ^ d * B + (j : ℝ) * ((N : ℝ) / (L : ℝ) ^ d * B) :=
          add_le_add h1 ih'
      _ = ((j : ℝ) + 1) * ((N : ℝ) / (L : ℝ) ^ d * B) := by ring
      _ = ((j + 1 : ℕ) : ℝ) * ((N : ℝ) / (L : ℝ) ^ d * B) := by push_cast; ring

end LatticeSystem.Quantum
