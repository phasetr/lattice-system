import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismStaggeredAlgebra
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSpinSymmetryRaising

/-!
# §10.2.3 (Theorem 10.6): `SU(2)` invariance of the squared staggered order parameter

The squared staggered order parameter of Tasaki eq. (10.2.16),

  `(Ô_L)² = Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y`   (`fermionStaggeredCasimirOp`),

is a sum of `SU(2)` scalars with scalar coefficients, hence commutes with the total-spin
generators used downstream:

  `[(Ô_L)², Ŝ³_tot] = [(Ô_L)², Ŝ⁺_tot] = 0`.

The proof is the double-sum reduction to the already-proved per-pair statements: each
two-site dot product `Ŝ_x · Ŝ_y` is an `SU(2)` scalar, so it commutes with `Ŝ³_tot`
(`totalSpinZ_commute_fermionSpinDot`) and with `Ŝ⁺_tot`
(`totalSpinPlus_commute_fermionSpinDot`); scaling by the staggered sign product `ε_x ε_y` and
summing over the ordered pairs preserves commutation.

This is the invariance ingredient of Tasaki's Theorem 10.6 argument: the `Ŝ³_tot` commutation
gives the weight-orthogonality of the ground-multiplet lowering tower
(`LiebFerrimagnetismGroundTower.lean`), and the `Ŝ⁺_tot` commutation feeds the ladder-ratio
transport (`LiebFerrimagnetismLadderRatio.lean`), which together reduce the ferrimagnetic bound
(10.2.17) for an arbitrary ground state to the centered-weight member of that tower.

This mirrors the spin-`S` template of §4.1 (Theorem 4.4, eq. (4.1.12),
`Quantum/SpinS/StaggeredCasimirSU2Invariance.lean`), transplanted to the fermionic carrier
`(Fin (2N+2) → Fin 2) → ℂ`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.3, p. 356, eqs. (10.2.16)/(10.2.17) (and the §4.1 template, eq. (4.1.12),
pp. 77–78).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

/-- **`[(Ô_L)², Ŝ³_tot] = 0`.**  Each per-pair dot product `Ŝ_x · Ŝ_y` is an `SU(2)` scalar and
commutes with `Ŝ³_tot`, so the signed double sum `Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y` does too. -/
theorem fermionStaggeredCasimirOp_commute_fermionTotalSpinZ (N : ℕ) (A : Finset (Fin (N + 1))) :
    Commute (fermionStaggeredCasimirOp N A) (fermionTotalSpinZ N) := by
  unfold fermionStaggeredCasimirOp
  exact Commute.sum_left _ _ _ fun x _ => Commute.sum_left _ _ _ fun y _ =>
    ((totalSpinZ_commute_fermionSpinDot N x y).symm).smul_left _

/-- **`[(Ô_L)², Ŝ⁺_tot] = 0`.**  Each per-pair dot product `Ŝ_x · Ŝ_y` commutes with the total
raising operator, so the signed double sum does too. -/
theorem fermionStaggeredCasimirOp_commute_fermionTotalSpinPlus (N : ℕ)
    (A : Finset (Fin (N + 1))) :
    Commute (fermionStaggeredCasimirOp N A) (fermionTotalSpinPlus N) := by
  unfold fermionStaggeredCasimirOp
  exact Commute.sum_left _ _ _ fun x _ => Commute.sum_left _ _ _ fun y _ =>
    ((totalSpinPlus_commute_fermionSpinDot N x y).symm).smul_left _

end LatticeSystem.Fermion
