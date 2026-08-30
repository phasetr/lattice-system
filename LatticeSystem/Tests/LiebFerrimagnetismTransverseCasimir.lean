import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismTransverseCasimir

/-!
# §10.2.3 Theorem 10.6 — transverse/Casimir identity (specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).)

Specification suite for
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebFerrimagnetismTransverseCasimir.lean`.
The `example` pins down the exact signature of
`sum_fermionSpinTransverse_eq_totalSpinSquared_sub_spinZ_sq`, mirroring the specification style of
`Tests/LiebFerrimagnetismStaggeredAlgebra.lean`, so that the implementation cannot silently
drift from the pinned statement.
-/

namespace LatticeSystem.Tests.LiebFerrimagnetismTransverseCasimir

open LatticeSystem.Fermion LatticeSystem.Quantum
open scoped BigOperators

/-! ## The transverse/Casimir double-sum identity:
`sum_fermionSpinTransverse_eq_totalSpinSquared_sub_spinZ_sq` -/

/-- **Transverse double sum = Casimir minus longitudinal square.**  Specializing PR-1's
`fermionStaggeredCasimirOp_eq_transverse_add_staggeredSpinZ_sq` at the trivial (all-`+1`) gauge
`A = Finset.univ` and composing with `fermionTotalSpinSquared_eq_sum_fermionSpinDot` and
`fermionTotalSpinZ_eq_sum_fermionSiteSpinZ` must give the un-staggered double-sum identity
`Σ_x Σ_y Ŝ⊥_{xy} = (Ŝ_tot)² − (Ŝ³_tot)²`. -/
example (N : ℕ) :
    ∑ x : Fin (N + 1), ∑ y : Fin (N + 1), fermionSpinTransverse N x y =
      fermionTotalSpinSquared N - fermionTotalSpinZ N * fermionTotalSpinZ N :=
  sum_fermionSpinTransverse_eq_totalSpinSquared_sub_spinZ_sq N

end LatticeSystem.Tests.LiebFerrimagnetismTransverseCasimir
