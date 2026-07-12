import LatticeSystem.Quantum.SpinS.AndersonTowerSphereAverage
import LatticeSystem.Math.SphereMoment
import LatticeSystem.Math.NoncommPowerExpansion
import Mathlib.Analysis.Matrix.Normed

/-!
# Tasaki §4.2: operator polynomial expansion of the direction sphere average (eq. (4.2.59))

For a unit vector `n ∈ S² ⊂ ℝ³` the direction order operator `Ô_L^n = Σ_x ε_x (Ŝ_x · n)`
(`directionStaggeredOp`) decomposes along the three spin axes as `Ô_L^n = Σ_α n_α ô^{(α)}`, where
`ô^{(α)}` is the axis-`α` staggered order operator (`stagOpVec`).  Raising to the `M`-th power and
integrating over the sphere, the noncommutative multinomial theorem
(`pow_sum_smul_eq_sum_smul_prod`) together with the scalar monomial moments
(`sphereMonomialMoment_eq`) yields

`∫_{S²} (Ô_L^n)^M dσ(n) = Σ_{f : Fin M → Fin 3} sphereMonomialMoment(count f) · ∏_j ô^{(f j)}`,

with the ordered operator product kept **literally** (`List.ofFn … |>.prod`); no commutators are
introduced (that contraction is deferred to the next step of the argument).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eq. (4.2.59), p.108 (operator expansion; scalar monomial moments are eq. (4.2.58)).
-/

namespace LatticeSystem.Quantum

open Matrix MeasureTheory LatticeSystem.Math
open scoped Matrix.Norms.Frobenius

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **axis-indexed staggered order operator vector** `α ↦ ô^{(α)}`: axis `0` is
`staggeredOrderOp1S`, axis `1` is `staggeredOrderOp2S`, axis `2` is the `3`-axis operator
`staggeredOrderOpS`.  It packages the three components so that `directionStaggeredOp` is the
`n`-weighted sum `Σ_α n_α ô^{(α)}` (`directionStaggeredOp_eq_sum`). -/
noncomputable def stagOpVec (A : Λ → Bool) (N : ℕ) : Fin 3 → ManyBodyOpS Λ N :=
  ![staggeredOrderOp1S A N, staggeredOrderOp2S A N, staggeredOrderOpS A N]

/-- **Axis decomposition of the direction order operator.**  For a unit vector
`n ∈ EuclideanSpace ℝ (Fin 3)`, the direction order operator `Ô_L^n` is the coordinate-weighted sum
`Σ_α n_α ô^{(α)}` of the three staggered axis operators. -/
theorem directionStaggeredOp_eq_sum (n : EuclideanSpace ℝ (Fin 3)) (A : Λ → Bool) (N : ℕ) :
    directionStaggeredOp n A N = ∑ α : Fin 3, ((n α : ℝ) : ℂ) • stagOpVec A N α := by
  rw [Fin.sum_univ_three]
  simp only [directionStaggeredOp, stagOpVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, staggeredOrderOp1S,
    staggeredOrderOp2S, staggeredOrderOpS, Finset.smul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  module

/-- **Tasaki eq. (4.2.59), operator polynomial expansion.**  The sphere average of the `M`-th power
of the direction order operator expands into a finite sum over index tuples `f : Fin M → Fin 3`,
each weighted by the scalar sphere monomial moment `sphereMonomialMoment(count f)` and multiplied by
the **ordered** product `∏_j ô^{(f j)}` of staggered axis operators.  Tuples with an odd axis
multiplicity contribute `0` (via `sphereMonomialMoment`); the operator order is preserved literally
(no commutators). -/
theorem sphereAverage_directionStaggeredOp_pow (A : Λ → Bool) (N M : ℕ) :
    (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ M ∂volume.toSphere)
      = ∑ f : Fin M → Fin 3,
          ((sphereMonomialMoment (fun α => (Finset.univ.filter (fun j => f j = α)).card) : ℝ) : ℂ) •
            (List.ofFn fun j => stagOpVec A N (f j)).prod := by
  have hpt : ∀ n : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ M
        = ∑ f : Fin M → Fin 3,
            (∏ j, (((n : EuclideanSpace ℝ (Fin 3)) (f j) : ℝ) : ℂ)) •
              (List.ofFn fun j => stagOpVec A N (f j)).prod := by
    intro n
    rw [directionStaggeredOp_eq_sum]
    exact pow_sum_smul_eq_sum_smul_prod
      (fun α => (((n : EuclideanSpace ℝ (Fin 3)) α : ℝ) : ℂ)) (fun α => stagOpVec A N α) M
  haveI : CompleteSpace (ManyBodyOpS Λ N) := FiniteDimensional.complete ℂ _
  have hcoord : ∀ i : Fin 3, Continuous
      (fun n : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =>
        (((n : EuclideanSpace ℝ (Fin 3)) i : ℝ) : ℂ)) := by
    intro i
    apply Complex.continuous_ofReal.comp
    exact (EuclideanSpace.proj i).continuous.comp continuous_subtype_val
  have hInt : ∀ f : Fin M → Fin 3,
      Integrable (fun n : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =>
        (∏ j, (((n : EuclideanSpace ℝ (Fin 3)) (f j) : ℝ) : ℂ)) •
          (List.ofFn fun j => stagOpVec A N (f j)).prod) volume.toSphere := fun f =>
    Continuous.integrable_of_hasCompactSupport
      ((continuous_finset_prod Finset.univ fun j _ => hcoord (f j)).smul continuous_const)
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _))
  simp_rw [hpt]
  rw [MeasureTheory.integral_finset_sum _ fun f _ => hInt f]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_smul_const]
  congr 1
  have hreal : ∫ n : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      ∏ j, ((n : EuclideanSpace ℝ (Fin 3)) (f j) : ℝ) ∂volume.toSphere
        = sphereMonomialMoment (fun α => (Finset.univ.filter (fun j => f j = α)).card) := by
    rw [← sphereMonomialMoment_eq (fun α => (Finset.univ.filter (fun j => f j = α)).card)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun n =>
      prod_comp_eq_prod_pow_card (fun i => ((n : EuclideanSpace ℝ (Fin 3)) i)) f)
  calc ∫ n : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
        (∏ j, (((n : EuclideanSpace ℝ (Fin 3)) (f j) : ℝ) : ℂ)) ∂volume.toSphere
      = ∫ n : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
          (((∏ j, ((n : EuclideanSpace ℝ (Fin 3)) (f j) : ℝ)) : ℝ) : ℂ) ∂volume.toSphere := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
        exact (Complex.ofReal_prod Finset.univ
          (fun j => ((n : EuclideanSpace ℝ (Fin 3)) (f j) : ℝ))).symm
    _ = (((∫ n : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
          ∏ j, ((n : EuclideanSpace ℝ (Fin 3)) (f j) : ℝ) ∂volume.toSphere) : ℝ) : ℂ) :=
        integral_complex_ofReal
    _ = ((sphereMonomialMoment
          (fun α => (Finset.univ.filter (fun j => f j = α)).card) : ℝ) : ℂ) := by
        rw [hreal]

/-- **Bochner–`mulVec` interchange for the direction order operator.**  The sphere Bochner integral
of the matrix-valued `k`-th power `(Ô_L^n)^k` commutes with right multiplication by a fixed
configuration vector `Φ`: integrating the vectors `(Ô_L^n)^k Φ` equals applying `·.mulVec Φ` to the
operator Bochner integral `∫_{S²} (Ô_L^n)^k dσ(n)`.  Since `M ↦ M.mulVec Φ` is a finite-dimensional
(hence continuous) `ℂ`-linear map, this is `ContinuousLinearMap.integral_comp_comm`; it linearizes
the operator expansion `sphereAverage_directionStaggeredOp_pow` onto the tower vector `Φ`. -/
theorem sphereAverage_directionStaggeredOp_pow_mulVec (A : Λ → Bool) (k : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) :
    (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ((directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ k).mulVec Φ
          ∂volume.toSphere)
      = (∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ k
            ∂volume.toSphere).mulVec Φ := by
  haveI : CompleteSpace (ManyBodyOpS Λ N) := FiniteDimensional.complete ℂ _
  -- Right multiplication by the fixed vector `Φ` as a continuous `ℂ`-linear map on operators.
  let L : ManyBodyOpS Λ N →ₗ[ℂ] ((Λ → Fin (N + 1)) → ℂ) :=
    { toFun := fun M => M.mulVec Φ
      map_add' := fun M₁ M₂ => Matrix.add_mulVec M₁ M₂ Φ
      map_smul' := fun c M => Matrix.smul_mulVec c M Φ }
  let Lc : ManyBodyOpS Λ N →L[ℂ] ((Λ → Fin (N + 1)) → ℂ) := ⟨L, L.continuous_of_finiteDimensional⟩
  -- The operator power is continuous in `n` and supported on the compact sphere, hence integrable.
  have hcoord : ∀ i : Fin 3, Continuous
      (fun n : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =>
        (((n : EuclideanSpace ℝ (Fin 3)) i : ℝ) : ℂ)) := fun i =>
    Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)
  have hdir : Continuous (fun n : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =>
      directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) := by
    refine continuous_finset_sum _ fun x _ => Continuous.smul continuous_const ?_
    exact (((hcoord 0).smul continuous_const).add ((hcoord 1).smul continuous_const)).add
      ((hcoord 2).smul continuous_const)
  have hInt : Integrable (fun n : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =>
      (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) A N) ^ k) volume.toSphere :=
    (hdir.pow k).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _))
  simpa only [Lc, L, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk] using
    Lc.integral_comp_comm hInt

end LatticeSystem.Quantum
