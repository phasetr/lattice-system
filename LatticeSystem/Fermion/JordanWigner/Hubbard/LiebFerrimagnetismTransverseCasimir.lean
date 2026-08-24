import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismStaggeredAlgebra
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveFermionSpinCasimirBridge

/-!
# §10.2.3 (Theorem 10.6): the transverse/Casimir identity

The transverse double sum `Σ_{x,y} Ŝ⊥_{xy}` (Tasaki eq. (10.2.7)) of the previous layer is not a
new operator: it is the *un-staggered* companion of `(Ô_L)²`, obtained from the staggered gauge by
the trivial choice `A = Λ`, where `ε_x ≡ +1`. Under that specialization the staggered operators of
the component-algebra layer collapse to the plain totals,

  `Ô^{(3)}_Λ = Σ_x Ŝ^z_x = Ŝ³_tot`,
  `(Ô_Λ)² = Σ_{x,y} Ŝ_x · Ŝ_y = (Ŝ_tot)²`,

so the staggered split `(Ô_L)² = (Ô_L)²_⊥ + (Ô^{(3)}_L)²` becomes the **transverse/Casimir
identity**

  `Σ_{x,y} Ŝ⊥_{xy} = (Ŝ_tot)² − (Ŝ³_tot)²`.

The weight band `m² ≤ γ` that selects the physical root `m = S₀` of the Casimir equation
`γ₀ = m(m + 1)` over its spurious companion `m = −(S₀ + 1)` is *not* restated here: it is the
existing `angMom_abs_le_J` (`Math/AngularMomentum/Ladder.lean`) applied through
`fermionTotalSpinSquared_posSemidef` and `fermionTotalSpinSquared_eq_cartesianSqSum`, the route
already used by `LiebRepulsiveMultipletCompanion.lean` and `LiebAttractiveFullSectorUnique.lean`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.3, p. 356, eqs. (10.2.16)/(10.2.17); §10.2.2, eq. (10.2.7), p. 351.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

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

end LatticeSystem.Fermion
