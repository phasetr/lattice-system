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

/-- **Transverse component equality** (P6, eq. 4.1.7 SU(2) invariance): for a total-`Ŝ³`-singlet
state (`Ŝ³_tot Φ = 0`), `⟨Φ, (Ô¹)² Φ⟩ = ⟨Φ, (Ô²)² Φ⟩`.  Via `[Ŝ³_tot, Ô¹Ô²] = i((Ô²)²−(Ô¹)²)` and
the Hermitian shift killing both sides on the singlet. -/
theorem staggeredOrder_sq_expectation_eq (A : Λ → Bool) (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    star Φ ⬝ᵥ (staggeredOrderOp1S A N * staggeredOrderOp1S A N).mulVec Φ
      = star Φ ⬝ᵥ (staggeredOrderOp2S A N * staggeredOrderOp2S A N).mulVec Φ := by
  have hS := totalSpinSOp3_isHermitian (Λ := Λ) (N := N)
  have hleib : totalSpinSOp3 Λ N * (staggeredOrderOp1S A N * staggeredOrderOp2S A N)
      - staggeredOrderOp1S A N * staggeredOrderOp2S A N * totalSpinSOp3 Λ N
      = Complex.I • (staggeredOrderOp2S A N * staggeredOrderOp2S A N
          - staggeredOrderOp1S A N * staggeredOrderOp1S A N) := by
    have e : totalSpinSOp3 Λ N * (staggeredOrderOp1S A N * staggeredOrderOp2S A N)
        - staggeredOrderOp1S A N * staggeredOrderOp2S A N * totalSpinSOp3 Λ N
        = (totalSpinSOp3 Λ N * staggeredOrderOp1S A N
            - staggeredOrderOp1S A N * totalSpinSOp3 Λ N) * staggeredOrderOp2S A N
          + staggeredOrderOp1S A N * (totalSpinSOp3 Λ N * staggeredOrderOp2S A N
            - staggeredOrderOp2S A N * totalSpinSOp3 Λ N) := by noncomm_ring
    rw [e, totalSpinSOp3_commutator_staggeredOrderOp1S,
      totalSpinSOp3_commutator_staggeredOrderOp2S, smul_mul_assoc, mul_smul_comm, neg_smul,
      ← sub_eq_add_neg, ← smul_sub]
  have hcomm0 : star Φ ⬝ᵥ (totalSpinSOp3 Λ N * (staggeredOrderOp1S A N * staggeredOrderOp2S A N)
      - staggeredOrderOp1S A N * staggeredOrderOp2S A N * totalSpinSOp3 Λ N).mulVec Φ = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, hermitian_dotProduct_shift hS, hsing, star_zero,
      zero_dotProduct, ← Matrix.mulVec_mulVec, hsing, Matrix.mulVec_zero, dotProduct_zero, sub_zero]
  rw [hleib, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hcomm0
  have h2 : star Φ ⬝ᵥ (staggeredOrderOp2S A N * staggeredOrderOp2S A N
      - staggeredOrderOp1S A N * staggeredOrderOp1S A N).mulVec Φ = 0 :=
    (mul_eq_zero.mp hcomm0).resolve_left Complex.I_ne_zero
  rw [Matrix.sub_mulVec, dotProduct_sub, sub_eq_zero] at h2
  exact h2.symm

end LatticeSystem.Quantum
