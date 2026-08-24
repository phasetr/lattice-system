import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismStaggeredAlgebra
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveFermionSpinCasimirBridge
import LatticeSystem.Math.CommutingHermitianEigenvector

/-!
# §10.2.3 (Theorem 10.6): the transverse/Casimir identity and the weight band

The transverse double sum `Σ_{x,y} Ŝ⊥_{xy}` (Tasaki eq. (10.2.7)) of the previous layer is not a
new operator: it is the *un-staggered* companion of `(Ô_L)²`, obtained from the staggered gauge by
the trivial choice `A = Λ`, where `ε_x ≡ +1`. Under that specialization the staggered operators of
the component-algebra layer collapse to the plain totals,

  `Ô^{(3)}_Λ = Σ_x Ŝ^z_x = Ŝ³_tot`,
  `(Ô_Λ)² = Σ_{x,y} Ŝ_x · Ŝ_y = (Ŝ_tot)²`,

so the staggered split `(Ô_L)² = (Ô_L)²_⊥ + (Ô^{(3)}_L)²` becomes the **transverse/Casimir
identity**

  `Σ_{x,y} Ŝ⊥_{xy} = (Ŝ_tot)² − (Ŝ³_tot)²`.

The right-hand side is positive semidefinite. Indeed the ladder definition
`(Ŝ_tot)² = Ŝ⁻Ŝ⁺ + Ŝ³(Ŝ³ + 1)` and the SU(2) commutator `Ŝ⁺Ŝ⁻ − Ŝ⁻Ŝ⁺ = 2Ŝ³` give the
anticommutator form

  `(Ŝ_tot)² − (Ŝ³_tot)² = Ŝ⁻Ŝ⁺ + Ŝ³ = ½(Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺)`,

whose two summands are the Hermitian squares `Ŝ⁺Ŝ⁻ = (Ŝ⁻)ᴴŜ⁻` and `Ŝ⁻Ŝ⁺ = (Ŝ⁺)ᴴŜ⁺`.

Evaluating that positive-semidefinite operator on a joint eigenvector of `Ŝ³_tot` (weight `m`) and
`(Ŝ_tot)²` (Casimir value `γ`) yields `(γ − m²)‖v‖² ≥ 0`, hence the **weight band**

  `m² ≤ γ`.

The band is what selects the physical root of the Casimir equation `γ₀ = m(m + 1)`: its two real
roots are `m = S₀` and the spurious top-weight companion `m = −(S₀ + 1)`, and only the former
satisfies `m² ≤ γ₀`. The multiplet-grading step of the ferrimagnetism argument therefore cannot
mistake the ground multiplet's top weight.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.3, p. 356, eqs. (10.2.16)/(10.2.17); §10.2.2, eq. (10.2.7), p. 351;
§11.1.1 (Casimir ladder form), p. 372.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

/-! ## The trivial gauge `A = Λ` -/

/-- On the full sublattice the gauge is trivial, `ε_x = +1` for every `x`. -/
private theorem gaugeSign_univ (N : ℕ) (x : Fin (N + 1)) :
    gaugeSign (Finset.univ : Finset (Fin (N + 1))) x = 1 := by
  rw [gaugeSign, if_pos (Finset.mem_univ x)]

/-- At the trivial gauge the longitudinal staggered operator is the total spin-`z`,
`Ô^{(3)}_Λ = Σ_x Ŝ^z_x = Ŝ³_tot`. -/
private theorem fermionStaggeredSpinZ_univ (N : ℕ) :
    fermionStaggeredSpinZ N (Finset.univ : Finset (Fin (N + 1))) = fermionTotalSpinZ N := by
  rw [fermionStaggeredSpinZ, fermionTotalSpinZ_eq_sum_fermionSiteSpinZ]
  exact Finset.sum_congr rfl fun x _ => by rw [gaugeSign_univ, one_smul]

/-- At the trivial gauge the transverse staggered double sum is the plain transverse double sum
`Σ_{x,y} Ŝ⊥_{xy}`. -/
private theorem fermionStaggeredTransverse_univ (N : ℕ) :
    fermionStaggeredTransverse N (Finset.univ : Finset (Fin (N + 1))) =
      ∑ x : Fin (N + 1), ∑ y : Fin (N + 1), fermionSpinTransverse N x y := by
  rw [fermionStaggeredTransverse]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [gaugeSign_univ, gaugeSign_univ, one_mul, one_smul]

/-- At the trivial gauge the squared staggered order parameter is the total-spin Casimir,
`(Ô_Λ)² = Σ_{x,y} Ŝ_x · Ŝ_y = (Ŝ_tot)²` (`fermionTotalSpinSquared_eq_sum_fermionSpinDot`). -/
private theorem fermionStaggeredCasimirOp_univ (N : ℕ) :
    fermionStaggeredCasimirOp N (Finset.univ : Finset (Fin (N + 1))) =
      fermionTotalSpinSquared N := by
  rw [fermionStaggeredCasimirOp, fermionTotalSpinSquared_eq_sum_fermionSpinDot]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [if_pos (Finset.mem_univ x), if_pos (Finset.mem_univ y), one_mul, one_smul]

/-! ## The transverse/Casimir identity -/

/-- **Transverse double sum = Casimir minus longitudinal square**,
`Σ_{x,y} Ŝ⊥_{xy} = (Ŝ_tot)² − (Ŝ³_tot)²`: the staggered transverse/longitudinal split
specialized to the trivial gauge `A = Λ`, where the staggered operators are the plain totals. -/
theorem sum_fermionSpinTransverse_eq_totalSpinSquared_sub_spinZ_sq (N : ℕ) :
    ∑ x : Fin (N + 1), ∑ y : Fin (N + 1), fermionSpinTransverse N x y =
      fermionTotalSpinSquared N - fermionTotalSpinZ N * fermionTotalSpinZ N := by
  have hsplit := fermionStaggeredCasimirOp_eq_transverse_add_staggeredSpinZ_sq N
    (Finset.univ : Finset (Fin (N + 1)))
  rw [fermionStaggeredCasimirOp_univ, fermionStaggeredTransverse_univ,
    fermionStaggeredSpinZ_univ] at hsplit
  rw [hsplit, add_sub_cancel_right]

/-! ## Positive semidefiniteness and the weight band -/

/-- **Anticommutator form of the transverse block.**  Substituting `Ŝ³ = ½(Ŝ⁺Ŝ⁻ − Ŝ⁻Ŝ⁺)` (the
SU(2) commutator) into `(Ŝ_tot)² − (Ŝ³_tot)² = Ŝ⁻Ŝ⁺ + Ŝ³` symmetrizes the ladder product. -/
private theorem fermionTotalSpinSquared_sub_spinZSq_eq_ladderAnticomm (N : ℕ) :
    fermionTotalSpinSquared N - fermionTotalSpinZ N * fermionTotalSpinZ N =
      (1 / 2 : ℂ) • (fermionTotalSpinPlus N * fermionTotalSpinMinus N +
        fermionTotalSpinMinus N * fermionTotalSpinPlus N) := by
  have hz : fermionTotalSpinZ N = (1 / 2 : ℂ) •
      (fermionTotalSpinPlus N * fermionTotalSpinMinus N -
        fermionTotalSpinMinus N * fermionTotalSpinPlus N) := by
    rw [fermionTotalSpinPlus_commutator_fermionTotalSpinMinus, smul_smul]
    norm_num
  rw [fermionTotalSpinSquared, mul_add, mul_one,
    show fermionTotalSpinMinus N * fermionTotalSpinPlus N +
          (fermionTotalSpinZ N * fermionTotalSpinZ N + fermionTotalSpinZ N) -
          fermionTotalSpinZ N * fermionTotalSpinZ N
        = fermionTotalSpinMinus N * fermionTotalSpinPlus N + fermionTotalSpinZ N from by abel,
    hz]
  module

/-- **The transverse block is positive semidefinite.**  `(Ŝ_tot)² − (Ŝ³_tot)²` equals
`½(Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺)`, a nonnegative multiple of the sum of the Hermitian squares
`Ŝ⁺Ŝ⁻ = (Ŝ⁻)ᴴŜ⁻` and `Ŝ⁻Ŝ⁺ = (Ŝ⁺)ᴴŜ⁺`. -/
theorem fermionTotalSpinSquared_sub_spinZSq_posSemidef (N : ℕ) :
    (fermionTotalSpinSquared N - fermionTotalSpinZ N * fermionTotalSpinZ N).PosSemidef := by
  rw [fermionTotalSpinSquared_sub_spinZSq_eq_ladderAnticomm]
  have hhalf : (0 : ℂ) ≤ (1 / 2 : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    exact RCLike.ofReal_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine Matrix.PosSemidef.smul (Matrix.PosSemidef.add ?_ ?_) hhalf
  · have h := Matrix.posSemidef_conjTranspose_mul_self (fermionTotalSpinMinus N)
    rwa [fermionTotalSpinMinus_conjTranspose] at h
  · have h := Matrix.posSemidef_conjTranspose_mul_self (fermionTotalSpinPlus N)
    rwa [fermionTotalSpinPlus_conjTranspose] at h

/-- **The weight band `m² ≤ γ`.**  On a nonzero joint eigenvector of `Ŝ³_tot` (weight `m`) and
`(Ŝ_tot)²` (Casimir value `γ`) the positive-semidefinite transverse block acts by the scalar
`γ − m²`, which is therefore nonnegative.  This excludes the spurious root `m = −(S₀ + 1)` of the
Casimir equation `γ₀ = m(m + 1)`. -/
theorem spinZ_sq_le_casimir_of_jointEigenvector (N : ℕ) (m γ : ℝ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (hv : v ≠ 0)
    (hz : (fermionTotalSpinZ N).mulVec v = (m : ℂ) • v)
    (hs : (fermionTotalSpinSquared N).mulVec v = (γ : ℂ) • v) :
    m ^ 2 ≤ γ := by
  have hdiff : (fermionTotalSpinSquared N - fermionTotalSpinZ N * fermionTotalSpinZ N).mulVec v
      = ((γ - m ^ 2 : ℝ) : ℂ) • v := by
    rw [Matrix.sub_mulVec, hs, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_smul, hz]
    push_cast
    module
  have hnonneg := Matrix.posSemidef_mulVec_eigenvalue_nonneg
    (fermionTotalSpinSquared_sub_spinZSq_posSemidef N) hv hdiff
  linarith

end LatticeSystem.Fermion
