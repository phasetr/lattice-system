import LatticeSystem.Quantum.SpinS.OrderOperatorAlgebra
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

/-- **Splitting a Hermitian power across a dot product**: for Hermitian `H`,
`⟨HᵃΦ, HᵇΦ⟩ = ⟨Φ, H^{a+b}Φ⟩`.  Lets the moments `⟨Φ, HᵏΦ⟩` be read as inner products of `H`-powers
of `Φ`, the input to the Cauchy–Schwarz moment inequalities. -/
theorem hermitian_pow_dotProduct_split {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (a b : ℕ) (Φ : n → ℂ) :
    star ((H ^ a).mulVec Φ) ⬝ᵥ ((H ^ b).mulVec Φ) = star Φ ⬝ᵥ (H ^ (a + b)).mulVec Φ := by
  rw [Matrix.star_mulVec, ← dotProduct_mulVec, (hH.pow a).eq, Matrix.mulVec_mulVec, ← pow_add]

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

end LatticeSystem.Quantum
