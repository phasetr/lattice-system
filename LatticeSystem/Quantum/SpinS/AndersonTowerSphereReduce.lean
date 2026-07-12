import LatticeSystem.Quantum.SpinS.AndersonTowerDirectionIsotropy
import LatticeSystem.Quantum.SpinS.AndersonTowerSphereMoment
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.RCLike.Basic

/-!
# Tasaki §4.2.2 Proposition 4.10: normalisation reduction of the solid-angle average (PR-6a)

The solid-angle average `Ξ_avg = solidAngleAverageTanaka d L N M Φ` (eq. (4.2.20)–(4.2.21)) is the
Bochner integral over the unit sphere of the direction symmetry-breaking states
`|Ξ_n⟩ = (1/√2)(unitNormalize((Ô_L^n)^M Φ) + unitNormalize((Ô_L^n)^{M+1} Φ))`.  This module reduces
the normalised average `unitNormalize(Ξ_avg)` to the normalisation of a single per-direction sphere
integral of the *even* power:

`unitNormalize(Ξ_avg) = unitNormalize((∫_{S²} (Ô_L^n)^{2j} dσ(n)) Φ)`, with
`2j = if Even M then M else M+1`.

The three ingredients (all under the singlet hypotheses `Ŝ³_tot Φ = Ŝ¹_tot Φ = 0`):

1. **Per-direction norm isotropy** (`directionTanakaTowerTerm_vecNormSqRe_indep`, sub-step L4b-iii):
   the squared norm `‖(Ô_L^n)^k Φ‖²` is `n`-independent, so `unitNormalize((Ô_L^n)^k Φ)` is a fixed
   positive-real multiple `c_k⁻¹` of `(Ô_L^n)^k Φ`, and the constant factors out of the sphere
   integral (`sphereIntegral_unitNormalize_directionTerm`).
2. **Bochner–`mulVec` interchange** (`sphereAverage_directionStaggeredOp_pow_mulVec`, sub-step L3):
   `∫_{S²} (Ô_L^n)^k Φ dσ(n) = (∫_{S²} (Ô_L^n)^k dσ(n)) Φ`.
3. **Odd vanishing** (`sphereMonomialMoment_odd`): the odd one of `{M, M+1}` integrates to the zero
   operator (`sphereAverageDirectionPow_odd_eq_zero`), so only the even power survives.

The degenerate case `c_{2j} = 0` (the even tower term vanishes identically) is handled internally:
both sides then normalise the zero vector, so no positivity hypothesis is carried.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.57)–(4.2.61), pp. 108–109.
-/

namespace LatticeSystem.Quantum

open Matrix MeasureTheory Filter LatticeSystem.Math
open scoped Matrix.Norms.Frobenius ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Elementary facts about `vecNormSqRe` and `unitNormalize` -/

/-- The squared `L²` norm is non-negative: `0 ≤ vecNormSqRe w`. -/
private theorem vecNormSqRe_nonneg {ι : Type*} [Fintype ι] (w : ι → ℂ) : 0 ≤ vecNormSqRe w := by
  have h := (Complex.le_def.mp (dotProduct_star_self_nonneg w)).1
  simpa [vecNormSqRe] using h

/-- A vector with vanishing squared `L²` norm is the zero vector: `vecNormSqRe w = 0 → w = 0`. -/
private theorem vecNormSqRe_eq_zero {ι : Type*} [Fintype ι] {w : ι → ℂ}
    (h : vecNormSqRe w = 0) : w = 0 := by
  unfold vecNormSqRe at h
  have him : (star w ⬝ᵥ w).im = 0 :=
    ((Complex.le_def.mp (dotProduct_star_self_nonneg w)).2).symm
  have hzero : star w ⬝ᵥ w = 0 := by
    apply Complex.ext
    · rw [Complex.zero_re]; exact h
    · rw [Complex.zero_im]; exact him
  exact dotProduct_star_self_eq_zero.mp hzero

/-- **`unitNormalize` is invariant under a positive real rescaling**:
`unitNormalize((t : ℂ) • v) = unitNormalize v` for `0 < t`.  The scalar `t` cancels between the
vector and its rescaled norm `√(t² ‖v‖²) = t ‖v‖`.  Exported (non-`private`) for reuse in the
sphere-average final assembly (Proposition 4.10, PR-6c), where the positive constant
`4π/(2j+1)` in front of `(ô²)ʲ Φ` is absorbed by the normalization. -/
theorem unitNormalize_ofReal_smul {ι : Type*} [Fintype ι] {t : ℝ} (ht : 0 < t)
    (v : ι → ℂ) : unitNormalize (((t : ℝ) : ℂ) • v) = unitNormalize v := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hnorm : vecNormSqRe (((t : ℝ) : ℂ) • v) = t ^ 2 * vecNormSqRe v := by
    unfold vecNormSqRe
    rw [star_smul_dotProduct_smul, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  rw [unitNormalize, unitNormalize, hnorm, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le,
    smul_smul]
  congr 1
  rw [Complex.ofReal_mul, mul_inv, mul_right_comm, inv_mul_cancel₀ htc, one_mul]

/-- The north pole `e₃ = (0,0,1)` lies on the unit sphere. -/
private theorem e3vec_mem_sphere : e3vec ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have h : ‖e3vec‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [e3vec_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Real.norm_eq_abs]
    norm_num
  have hsq := Real.sqrt_sq (norm_nonneg e3vec)
  rw [h, Real.sqrt_one] at hsq
  exact hsq.symm

/-! ### Continuity of the per-direction tower vector -/

/-- The per-direction tower vector `n ↦ (Ô_L^n)^k Φ` is continuous on the sphere: the direction
operator `Ô_L^n` depends continuously (polynomially) on `n`, and both taking the `k`-th power and
right-multiplying the fixed vector `Φ` are continuous. -/
private theorem continuous_directionTerm (A : Λ → Bool) (k : ℕ) (Φ : (Λ → Fin (N + 1)) → ℂ) :
    Continuous (fun n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      ((directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ k).mulVec Φ) := by
  have hcoord : ∀ i : Fin 3, Continuous
      (fun n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        (((n : EuclideanSpace ℝ (Fin 3)) i : ℝ) : ℂ)) := fun i =>
    Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)
  have hdir : Continuous (fun n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) := by
    refine continuous_finset_sum _ fun x _ => Continuous.smul continuous_const ?_
    exact (((hcoord 0).smul continuous_const).add ((hcoord 1).smul continuous_const)).add
      ((hcoord 2).smul continuous_const)
  exact (hdir.pow k).matrix_mulVec continuous_const

/-! ### Odd powers integrate to the zero operator -/

/-- **Odd sphere power vanishing.**  For an odd exponent `k`, every index tuple `f : Fin k → Fin 3`
has an axis with odd multiplicity (the multiplicities sum to `k`), so its sphere monomial moment
vanishes (`sphereMonomialMoment` odd case); hence the whole operator expansion
(`sphereAverage_directionStaggeredOp_pow`) of `∫_{S²} (Ô_L^n)^k dσ(n)` is the zero operator. -/
private theorem sphereAverageDirectionPow_odd_eq_zero (A : Λ → Bool) (k : ℕ) (hk : Odd k) :
    (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ k ∂volume.toSphere) = 0 := by
  classical
  rw [sphereAverage_directionStaggeredOp_pow]
  refine Finset.sum_eq_zero (fun f _ => ?_)
  have hcard : ∑ α : Fin 3, (Finset.univ.filter (fun j => f j = α)).card = k := by
    have H := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin k))) (t := (Finset.univ : Finset (Fin 3)))
      (f := f) (fun x _ => Finset.mem_univ (f x))
    simpa [Finset.card_univ, Fintype.card_fin] using H.symm
  have hnotall : ¬ ∀ i : Fin 3, Even ((Finset.univ.filter (fun j => f j = i)).card) := by
    intro hall
    have heven : Even (∑ α : Fin 3, (Finset.univ.filter (fun j => f j = α)).card) :=
      Finset.even_sum _ (fun α _ => hall α)
    rw [hcard] at heven
    exact (Nat.not_even_iff_odd.mpr hk) heven
  have hmom : sphereMonomialMoment (fun α => (Finset.univ.filter (fun j => f j = α)).card) = 0 := by
    unfold sphereMonomialMoment
    rw [if_neg hnotall]
  rw [hmom]
  simp only [Complex.ofReal_zero, zero_smul]

/-! ### The per-direction normalisation reduces to a fixed scalar multiple -/

/-- **Sphere integral of the per-direction normalised tower vector.**  Under the singlet hypotheses
the squared norm `‖(Ô_L^n)^k Φ‖²` is `n`-independent
(`directionTanakaTowerTerm_vecNormSqRe_indep`), so the normalisation
`unitNormalize((Ô_L^n)^k Φ) = c_k⁻¹ • (Ô_L^n)^k Φ` has the *fixed* scalar `c_k⁻¹`, with
`c_k = √(‖(Ô_L^{e₃})^k Φ‖²)`.  The scalar factors out of the Bochner integral, which then
reduces via `sphereAverage_directionStaggeredOp_pow_mulVec` to `c_k⁻¹ • (∫_{S²}(Ô_L^n)^k) Φ`. -/
private theorem sphereIntegral_unitNormalize_directionTerm (A : Λ → Bool) (k : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        unitNormalize (directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N k Φ)
          ∂volume.toSphere)
      = ((Real.sqrt (vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ)) : ℝ) : ℂ)⁻¹
          • (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
              (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ k
                ∂volume.toSphere).mulVec Φ := by
  have hpt : ∀ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      unitNormalize (directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N k Φ)
        = ((Real.sqrt (vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ)) : ℝ) : ℂ)⁻¹
            • directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N k Φ := by
    intro n
    have hEq : vecNormSqRe (directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N k Φ)
        = vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ) :=
      directionTanakaTowerTerm_vecNormSqRe_indep A k Φ h3 h1 n (Subtype.mk e3vec e3vec_mem_sphere)
    rw [unitNormalize, hEq]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_smul]
  congr 1
  simp only [directionTanakaTowerTerm]
  exact sphereAverage_directionStaggeredOp_pow_mulVec A k Φ

/-- **Integrability of the per-direction normalised tower vector.**  It agrees everywhere with the
continuous function `c_k⁻¹ • (Ô_L^n)^k Φ` (`hpt`), which is integrable on the compact sphere. -/
private theorem integrable_unitNormalize_directionTerm (A : Λ → Bool) (k : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    Integrable (fun n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      unitNormalize (directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N k Φ))
      volume.toSphere := by
  have hpt : ∀ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      unitNormalize (directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N k Φ)
        = ((Real.sqrt (vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ)) : ℝ) : ℂ)⁻¹
            • directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N k Φ := by
    intro n
    have hEq : vecNormSqRe (directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N k Φ)
        = vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ) :=
      directionTanakaTowerTerm_vecNormSqRe_indep A k Φ h3 h1 n (Subtype.mk e3vec e3vec_mem_sphere)
    rw [unitNormalize, hEq]
  have hcont : Continuous (fun n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
      ((Real.sqrt (vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ)) : ℝ) : ℂ)⁻¹
        • directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N k Φ) := by
    simp only [directionTanakaTowerTerm]
    exact continuous_const.smul (continuous_directionTerm A k Φ)
  exact (hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _))).congr
    (Filter.Eventually.of_forall (fun n => (hpt n).symm))

/-- If the even tower term vanishes identically (`c_{2j} = 0`), the even sphere power vector is the
zero vector.  By norm isotropy `‖(Ô_L^n)^k Φ‖² = 0` for every `n`, so each `(Ô_L^n)^k Φ` is zero and
the Bochner integral (via `sphereAverage_directionStaggeredOp_pow_mulVec`) vanishes. -/
private theorem directionOrderPow_mulVec_eq_zero_of_vecNormSqRe_eq_zero (A : Λ → Bool) (k : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0)
    (hQ : vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ) = 0) :
    (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ k
          ∂volume.toSphere).mulVec Φ = 0 := by
  have hz : ∀ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ((directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ k).mulVec Φ = 0 := by
    intro n
    have hEq : vecNormSqRe (directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N k Φ)
        = vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ) :=
      directionTanakaTowerTerm_vecNormSqRe_indep A k Φ h3 h1 n (Subtype.mk e3vec e3vec_mem_sphere)
    have hzero : directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) A N k Φ = 0 :=
      vecNormSqRe_eq_zero (by rw [hEq]; exact hQ)
    simpa [directionTanakaTowerTerm] using hzero
  rw [← sphereAverage_directionStaggeredOp_pow_mulVec A k Φ,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hz), MeasureTheory.integral_zero]

/-- **Scalar collapse of the normalised even sphere power.**  The two positive-real rescalings
`(1/√2)` and `c_k⁻¹` are absorbed by `unitNormalize`; the degenerate case `c_k = 0` (even term
vanishing) makes both sides normalise the zero vector. -/
private theorem unitNormalize_sqrt2Inv_directionOrder_eq (A : Λ → Bool) (k : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    unitNormalize (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
        (((Real.sqrt (vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ)) : ℝ) : ℂ)⁻¹
          • (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
              (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ k
                ∂volume.toSphere).mulVec Φ))
      = unitNormalize ((∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ k
            ∂volume.toSphere).mulVec Φ) := by
  by_cases hQ0 : vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ) = 0
  · rw [directionOrderPow_mulVec_eq_zero_of_vecNormSqRe_eq_zero A k Φ h3 h1 hQ0,
      smul_zero, smul_zero]
  · have hQpos : 0 < vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ) :=
      lt_of_le_of_ne (vecNormSqRe_nonneg _) (Ne.symm hQ0)
    have hs : 0 < Real.sqrt 2
        * Real.sqrt (vecNormSqRe (directionTanakaTowerTerm e3vec A N k Φ)) :=
      mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr hQpos)
    rw [smul_smul, ← mul_inv, ← Complex.ofReal_mul, ← Complex.ofReal_inv]
    exact unitNormalize_ofReal_smul (inv_pos.mpr hs) _

/-! ### The sphere-average normalisation reduction (PR-6a tip) -/

/-- **Normalisation reduction of the solid-angle average** (Tasaki §4.2.2, PR-6a).  For a total-spin
singlet `Φ` (`Ŝ³_tot Φ = Ŝ¹_tot Φ = 0`) the normalised solid-angle average of the direction
symmetry-breaking states equals the normalisation of the single even-power sphere integral
applied to `Φ`:

`unitNormalize(Ξ_avg) = unitNormalize((∫_{S²} (Ô_L^n)^{2j} dσ(n)) Φ)`, with
`2j = if Even M then M else M+1`.

The odd one of the two adjacent powers `{M, M+1}` integrates to the zero operator
(`sphereAverageDirectionPow_odd_eq_zero`); the even one survives with a fixed positive-real
normalisation constant that `unitNormalize` absorbs (`unitNormalize_sqrt2Inv_directionOrder_eq`),
handling the degenerate vanishing case internally.  This is the tip consumed by the vector remainder
bridge (PR-6b) and the final assembly (PR-6c). -/
theorem solidAngleAverageTanaka_unitNormalize_eq_orderPow (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (h3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0) :
    unitNormalize (solidAngleAverageTanaka d L N M Φ)
      = unitNormalize ((∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) (torusParitySublattice d L) N)
            ^ (if Even M then M else M + 1) ∂volume.toSphere).mulVec Φ) := by
  have hExpand : solidAngleAverageTanaka d L N M Φ
      = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
          ((((Real.sqrt (vecNormSqRe (directionTanakaTowerTerm e3vec
                (torusParitySublattice d L) N M Φ)) : ℝ) : ℂ)⁻¹
              • (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
                  (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3))
                    (torusParitySublattice d L) N) ^ M ∂volume.toSphere).mulVec Φ)
            + (((Real.sqrt (vecNormSqRe (directionTanakaTowerTerm e3vec
                (torusParitySublattice d L) N (M + 1) Φ)) : ℝ) : ℂ)⁻¹
              • (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
                  (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3))
                    (torusParitySublattice d L) N) ^ (M + 1) ∂volume.toSphere).mulVec Φ)) := by
    simp only [solidAngleAverageTanaka, directionTanakaState]
    rw [MeasureTheory.integral_smul,
      MeasureTheory.integral_add
        (integrable_unitNormalize_directionTerm (torusParitySublattice d L) M Φ h3 h1)
        (integrable_unitNormalize_directionTerm (torusParitySublattice d L) (M + 1) Φ h3 h1),
      sphereIntegral_unitNormalize_directionTerm (torusParitySublattice d L) M Φ h3 h1,
      sphereIntegral_unitNormalize_directionTerm (torusParitySublattice d L) (M + 1) Φ h3 h1]
  rw [hExpand]
  by_cases hM : Even M
  · rw [sphereAverageDirectionPow_odd_eq_zero (torusParitySublattice d L) (M + 1) hM.add_one,
      Matrix.zero_mulVec, smul_zero, add_zero, if_pos hM]
    exact unitNormalize_sqrt2Inv_directionOrder_eq (torusParitySublattice d L) M Φ h3 h1
  · rw [sphereAverageDirectionPow_odd_eq_zero (torusParitySublattice d L) M
        (Nat.not_even_iff_odd.mp hM), Matrix.zero_mulVec, smul_zero, zero_add, if_neg hM]
    exact unitNormalize_sqrt2Inv_directionOrder_eq (torusParitySublattice d L) (M + 1) Φ h3 h1

end LatticeSystem.Quantum
