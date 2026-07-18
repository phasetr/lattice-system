import LatticeSystem.Quantum.SpinS.AndersonTower
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The many-body `L²` operator norm

This file provides the genuine `L²` operator norm for finite-dimensional many-body operators and
its foundational algebraic, vector-bound, and unitary-conjugation API.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **`L²` operator (spectral) norm** of a many-body operator, via the associated continuous
linear map on `EuclideanSpace ℂ (Λ → Fin (N+1))`.  This is submultiplicative and satisfies the
triangle inequality — unlike the default entrywise matrix norm — so it is the correct norm for the
order-operator bounds. -/
noncomputable def manyBodyOperatorNormS (M : ManyBodyOpS Λ N) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖

/-- **Bridge to the bundled star-algebra image**: the many-body `L²` operator norm equals the
operator norm of the continuous-linear-map image `Matrix.toEuclideanCLM M` (the two coincide because
`toEuclideanCLM` is the bundled `toContinuousLinearMap ∘ toEuclideanLin`).  Routing through the
`StarAlgEquiv` `toEuclideanCLM` lets the norm-algebra inequalities follow from the continuous-linear
endomorphism `NormedRing`. -/
theorem manyBodyOperatorNormS_eq_toEuclideanCLM (M : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS M = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖ := by
  rw [manyBodyOperatorNormS]
  congr 1

/-- The many-body `L²` operator norm is nonnegative. -/
theorem manyBodyOperatorNormS_nonneg (M : ManyBodyOpS Λ N) : 0 ≤ manyBodyOperatorNormS M :=
  norm_nonneg _

/-- The many-body `L²` operator norm of `0` is `0`. -/
@[simp] theorem manyBodyOperatorNormS_zero : manyBodyOperatorNormS (0 : ManyBodyOpS Λ N) = 0 := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, map_zero, norm_zero]

/-- The many-body `L²` operator norm is invariant under negation. -/
theorem manyBodyOperatorNormS_neg (M : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (-M) = manyBodyOperatorNormS M := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, manyBodyOperatorNormS_eq_toEuclideanCLM, map_neg,
    norm_neg]

/-- **Triangle inequality** for the many-body `L²` operator norm. -/
theorem manyBodyOperatorNormS_add_le (M₁ M₂ : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (M₁ + M₂) ≤ manyBodyOperatorNormS M₁ + manyBodyOperatorNormS M₂ := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, manyBodyOperatorNormS_eq_toEuclideanCLM,
    manyBodyOperatorNormS_eq_toEuclideanCLM, map_add]
  exact norm_add_le _ _

/-- **Subtraction triangle inequality** for the many-body `L²` operator norm. -/
theorem manyBodyOperatorNormS_sub_le (M₁ M₂ : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (M₁ - M₂) ≤ manyBodyOperatorNormS M₁ + manyBodyOperatorNormS M₂ := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, manyBodyOperatorNormS_eq_toEuclideanCLM,
    manyBodyOperatorNormS_eq_toEuclideanCLM, map_sub]
  exact norm_sub_le _ _

/-- **Three-term triangle inequality** for the difference, via an intermediate operator. -/
theorem manyBodyOperatorNormS_sub_le' (x y z : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (x - z)
      ≤ manyBodyOperatorNormS (x - y) + manyBodyOperatorNormS (y - z) := by
  rw [show x - z = (x - y) + (y - z) from by abel]
  exact manyBodyOperatorNormS_add_le _ _

/-- **Scalar homogeneity** of the many-body `L²` operator norm. -/
theorem manyBodyOperatorNormS_smul (c : ℂ) (M : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (c • M) = ‖c‖ * manyBodyOperatorNormS M := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, manyBodyOperatorNormS_eq_toEuclideanCLM, map_smul,
    norm_smul]

/-- **Submultiplicativity** of the many-body `L²` operator norm. -/
theorem manyBodyOperatorNormS_mul_le (M₁ M₂ : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (M₁ * M₂) ≤ manyBodyOperatorNormS M₁ * manyBodyOperatorNormS M₂ := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, manyBodyOperatorNormS_eq_toEuclideanCLM,
    manyBodyOperatorNormS_eq_toEuclideanCLM, map_mul]
  exact norm_mul_le _ _

/-- **Power submultiplicativity** of the many-body `L²` operator norm (for `n > 0`). -/
theorem manyBodyOperatorNormS_pow_le (M : ManyBodyOpS Λ N) {n : ℕ} (hn : 0 < n) :
    manyBodyOperatorNormS (M ^ n) ≤ manyBodyOperatorNormS M ^ n := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, map_pow, manyBodyOperatorNormS_eq_toEuclideanCLM]
  exact norm_pow_le' _ hn

/-- **List-product submultiplicativity**: the norm of an ordered product is at most the product of
the norms.  Used to bound `balancedOrderProductS`. -/
theorem manyBodyOperatorNormS_list_prod_le (l : List (ManyBodyOpS Λ N)) :
    manyBodyOperatorNormS l.prod ≤ (l.map manyBodyOperatorNormS).prod := by
  induction l with
  | nil => simp [manyBodyOperatorNormS_eq_toEuclideanCLM]
  | cons a t ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    refine le_trans (manyBodyOperatorNormS_mul_le a t.prod) ?_
    exact mul_le_mul_of_nonneg_left ih (manyBodyOperatorNormS_nonneg a)

/-- **Finite-sum triangle inequality** for the many-body `L²` operator norm. -/
theorem manyBodyOperatorNormS_sum_le {ι : Type*} (s : Finset ι) (f : ι → ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (∑ x ∈ s, f x) ≤ ∑ x ∈ s, manyBodyOperatorNormS (f x) := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, map_sum]
  refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun x _ => (manyBodyOperatorNormS_eq_toEuclideanCLM (f x)).symm)

/-- **Operator-norm vector bound** `‖G v‖₂ ≤ ‖G‖_op ‖v‖₂`.  Routing `G.mulVec`
through the bundled continuous-linear-map image `Matrix.toEuclideanCLM` and applying
`ContinuousLinearMap.le_opNorm`.  This is the plain vector-norm companion to the
inner-product Cauchy–Schwarz form `abs_re_dotProduct_mulVec_le_norm_mul`. -/
theorem mulVec_toLp_norm_le (G : ManyBodyOpS Λ N) (v : (Λ → Fin (N + 1)) → ℂ) :
    ‖(WithLp.toLp 2 (G.mulVec v) : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖
      ≤ manyBodyOperatorNormS G
          * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM]
  have h := ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (𝕜 := ℂ) G)
    (WithLp.toLp 2 v : EuclideanSpace ℂ (Λ → Fin (N + 1)))
  rwa [Matrix.toEuclideanCLM_toLp] at h

/-- **`vecNormSqRe` as a squared `L²` norm**: `√(vecNormSqRe w) = ‖toLp 2 w‖`, since
`vecNormSqRe w = ⟨w, w⟩.re = ‖toLp 2 w‖²` and the square root of a square is the
(nonnegative) norm.  The bridge from the real self-pairing to the Euclidean `L²` norm. -/
theorem sqrt_vecNormSqRe_eq_toLp_norm (w : (Λ → Fin (N + 1)) → ℂ) :
    Real.sqrt (vecNormSqRe w)
      = ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ := by
  have hsq : vecNormSqRe w
      = ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖
        * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ := by
    rw [vecNormSqRe]
    have h := inner_self_eq_norm_mul_norm (𝕜 := ℂ)
      (WithLp.toLp 2 w : EuclideanSpace ℂ (Λ → Fin (N + 1)))
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [dotProduct_comm] at h
    simpa using h
  rw [hsq]
  exact Real.sqrt_mul_self (norm_nonneg _)

/-- **`vecNormSqRe` operator-norm vector bound**
`√(vecNormSqRe (G v)) ≤ ‖G‖_op √(vecNormSqRe v)`: the `vecNormSqRe` form of
`mulVec_toLp_norm_le`, obtained by rewriting each `√(vecNormSqRe ·)` as an `L²` norm via
`sqrt_vecNormSqRe_eq_toLp_norm`. -/
theorem sqrt_vecNormSqRe_mulVec_le (G : ManyBodyOpS Λ N) (v : (Λ → Fin (N + 1)) → ℂ) :
    Real.sqrt (vecNormSqRe (G.mulVec v))
      ≤ manyBodyOperatorNormS G * Real.sqrt (vecNormSqRe v) := by
  rw [sqrt_vecNormSqRe_eq_toLp_norm, sqrt_vecNormSqRe_eq_toLp_norm]
  exact mulVec_toLp_norm_le G v

section L2Wrappers
open scoped Matrix.Norms.L2Operator

/-- The many-body `L²` operator norm coincides with the scoped `Matrix.Norms.L2Operator` norm. -/
theorem manyBodyOperatorNormS_eq_l2 (M : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS M = ‖M‖ := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, Matrix.l2_opNorm_toEuclideanCLM]

/-- The many-body `L²` operator norm is invariant under conjugate transpose. -/
theorem manyBodyOperatorNormS_conjTranspose (M : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (Matrix.conjTranspose M) = manyBodyOperatorNormS M := by
  rw [manyBodyOperatorNormS_eq_l2, manyBodyOperatorNormS_eq_l2, Matrix.l2_opNorm_conjTranspose]

/-- `C*`-identity for the many-body `L²` operator norm: `‖MᴴM‖ = ‖M‖²`. -/
theorem manyBodyOperatorNormS_conjTranspose_mul_self (M : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (Matrix.conjTranspose M * M) = manyBodyOperatorNormS M ^ 2 := by
  rw [manyBodyOperatorNormS_eq_l2, manyBodyOperatorNormS_eq_l2,
    Matrix.l2_opNorm_conjTranspose_mul_self, sq]

/-- The `L²` operator norm of a diagonal many-body operator bounded by `C` when every entry is. -/
theorem manyBodyOperatorNormS_diagonal_le {v : (Λ → Fin (N + 1)) → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ σ, ‖v σ‖ ≤ C) : manyBodyOperatorNormS (Matrix.diagonal v) ≤ C := by
  rw [manyBodyOperatorNormS_eq_l2, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).2 h

end L2Wrappers

/-- The many-body `L²` operator norm of the identity is `1` (the bundled `toEuclideanCLM` sends `1`
to the identity endomorphism, whose operator norm is `1` on the nontrivial space). -/
@[simp] theorem manyBodyOperatorNormS_one :
    manyBodyOperatorNormS (1 : ManyBodyOpS Λ N) = 1 := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM, map_one, norm_one]

/-- **Unitary conjugation preserves the many-body `L²` operator norm**: if `UᴴU = 1` then
`‖U Y Uᴴ‖ = ‖Y‖`.  The forward bound is two submultiplicative steps with `‖U‖ = 1` (from the
`C*`-identity `‖UᴴU‖ = ‖U‖²` and `‖1‖ = 1`) and `‖Uᴴ‖ = ‖U‖`; the reverse bound rewrites
`Y = Uᴴ (U Y Uᴴ) U = (UᴴU) Y (UᴴU)`.  Consumed by the second-order twist-conjugation bound of the
generalized Lieb–Schultz–Mattis Lemma 6.4 (Tasaki §6.2). -/
theorem manyBodyOperatorNormS_unitary_conj {U Y : ManyBodyOpS Λ N}
    (hU : Matrix.conjTranspose U * U = 1) :
    manyBodyOperatorNormS (U * Y * Matrix.conjTranspose U) = manyBodyOperatorNormS Y := by
  have hUnorm : manyBodyOperatorNormS U = 1 := by
    have h := manyBodyOperatorNormS_conjTranspose_mul_self U
    rw [hU, manyBodyOperatorNormS_one] at h
    rw [← Real.sqrt_sq (manyBodyOperatorNormS_nonneg U), ← h, Real.sqrt_one]
  have hY : Matrix.conjTranspose U * (U * Y * Matrix.conjTranspose U) * U = Y := by
    calc Matrix.conjTranspose U * (U * Y * Matrix.conjTranspose U) * U
        = (Matrix.conjTranspose U * U) * (Y * (Matrix.conjTranspose U * U)) := by
          simp only [mul_assoc]
      _ = Y := by rw [hU, one_mul, mul_one]
  refine le_antisymm ?_ ?_
  · calc manyBodyOperatorNormS (U * Y * Matrix.conjTranspose U)
        ≤ manyBodyOperatorNormS (U * Y) * manyBodyOperatorNormS (Matrix.conjTranspose U) :=
          manyBodyOperatorNormS_mul_le _ _
      _ ≤ manyBodyOperatorNormS U * manyBodyOperatorNormS Y
            * manyBodyOperatorNormS (Matrix.conjTranspose U) :=
          mul_le_mul_of_nonneg_right (manyBodyOperatorNormS_mul_le _ _)
            (manyBodyOperatorNormS_nonneg _)
      _ = manyBodyOperatorNormS Y := by rw [manyBodyOperatorNormS_conjTranspose, hUnorm]; ring
  · calc manyBodyOperatorNormS Y
        = manyBodyOperatorNormS
            (Matrix.conjTranspose U * (U * Y * Matrix.conjTranspose U) * U) := by rw [hY]
      _ ≤ manyBodyOperatorNormS (Matrix.conjTranspose U * (U * Y * Matrix.conjTranspose U))
            * manyBodyOperatorNormS U := manyBodyOperatorNormS_mul_le _ _
      _ ≤ manyBodyOperatorNormS (Matrix.conjTranspose U)
            * manyBodyOperatorNormS (U * Y * Matrix.conjTranspose U) * manyBodyOperatorNormS U :=
          mul_le_mul_of_nonneg_right (manyBodyOperatorNormS_mul_le _ _)
            (manyBodyOperatorNormS_nonneg _)
      _ = manyBodyOperatorNormS (U * Y * Matrix.conjTranspose U) := by
          rw [manyBodyOperatorNormS_conjTranspose, hUnorm]; ring

end LatticeSystem.Quantum
