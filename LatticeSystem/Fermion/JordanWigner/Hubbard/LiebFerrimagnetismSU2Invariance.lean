import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismStaggeredAlgebra
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSpinSymmetryRaising

/-!
# §10.2.3 (Theorem 10.6): `SU(2)` invariance of the squared staggered order parameter

The squared staggered order parameter of Tasaki eq. (10.2.16),

  `(Ô_L)² = Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y`   (`fermionStaggeredCasimirOp`),

is a sum of `SU(2)` scalars with scalar coefficients, hence commutes with every total-spin
generator:

  `[(Ô_L)², Ŝ³_tot] = [(Ô_L)², Ŝ⁺_tot] = [(Ô_L)², Ŝ⁻_tot] = 0`.

The proof is the double-sum reduction to the already-proved per-pair statements: each
two-site dot product `Ŝ_x · Ŝ_y` is an `SU(2)` scalar, so it commutes with `Ŝ³_tot`
(`totalSpinZ_commute_fermionSpinDot`) and with `Ŝ⁺_tot`
(`totalSpinPlus_commute_fermionSpinDot`); scaling by the staggered sign product `ε_x ε_y` and
summing over the ordered pairs preserves commutation.  The lowering generator is obtained from
the raising one by taking conjugate transposes of `(Ô_L)² Ŝ⁺_tot = Ŝ⁺_tot (Ô_L)²`, using
`(Ŝ⁺_tot)ᴴ = Ŝ⁻_tot` (`fermionTotalSpinPlus_conjTranspose`) together with the self-adjointness of
`(Ô_L)²` (`fermionStaggeredCasimirOp_isHermitian`).

This is the invariance ingredient of Tasaki's Theorem 10.6 argument: since `(Ô_L)²` commutes with
the full `SU(2)` action, its expectation is transported along the lowering tower of the ground
multiplet, which reduces the ferrimagnetic bound (10.2.17) for an arbitrary ground state to the
centered-weight member of that tower.

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

/-- **`[(Ô_L)², Ŝ⁻_tot] = 0`.**  Conjugate transpose of the raising statement: `(Ŝ⁺_tot)ᴴ =
Ŝ⁻_tot` and `(Ô_L)²` is self-adjoint, so `Ŝ⁻_tot (Ô_L)² = (Ô_L)² Ŝ⁻_tot`.  As in
`fermionTotalSpinMinus_commute_symmetricRepulsiveHubbardHamiltonian`, the transposing step must
spell `Matrix.conjTranspose` out, since `congrArg` needs an explicit function argument. -/
theorem fermionStaggeredCasimirOp_commute_fermionTotalSpinMinus (N : ℕ)
    (A : Finset (Fin (N + 1))) :
    Commute (fermionStaggeredCasimirOp N A) (fermionTotalSpinMinus N) := by
  have h_adj := congrArg Matrix.conjTranspose
    (fermionStaggeredCasimirOp_commute_fermionTotalSpinPlus N A).eq
  simp only [Matrix.conjTranspose_mul, fermionTotalSpinPlus_conjTranspose N,
    (fermionStaggeredCasimirOp_isHermitian N A).eq] at h_adj
  exact h_adj.symm

end LatticeSystem.Fermion
