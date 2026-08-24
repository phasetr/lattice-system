import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismSU2Invariance

/-!
# §10.2.3 Theorem 10.6 — `SU(2)` invariance of `Ô²` (specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).)

Specification suite for
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebFerrimagnetismSU2Invariance.lean`.
The `example`s pin down the exact signatures of
`fermionStaggeredCasimirOp_commute_fermionTotalSpinZ`,
`fermionStaggeredCasimirOp_commute_fermionTotalSpinPlus` and
`fermionStaggeredCasimirOp_commute_fermionTotalSpinMinus`, mirroring PR-1/PR-2's specification
style (`Tests/LiebFerrimagnetismStaggeredAlgebra.lean`,
`Tests/LiebFerrimagnetismTransverseCasimir.lean`) and the discharged SpinS template
`Quantum/SpinS/StaggeredCasimirSU2Invariance.lean`, so that the implementation cannot silently
drift from the design's exact statements
(`.self-local/docs/theorem-10-6-design.md`, PR-3 section).
-/

namespace LatticeSystem.Tests.LiebFerrimagnetismSU2Invariance

open LatticeSystem.Fermion LatticeSystem.Quantum
open scoped BigOperators

/-! ## `SU(2)` invariance of `Ô² = fermionStaggeredCasimirOp` -/

/-- **`[Ô², Ŝ³_tot] = 0`.** The squared staggered Casimir operator commutes with the total
`z`-spin generator: each per-pair `fermionSpinDot x y` commutes with `Ŝ³_tot`
(`totalSpinZ_commute_fermionSpinDot`, `TJSpinSymmetry.lean:207`), so the signed double sum
`Ô² = Σ_{x,y} ε_x ε_y Ŝ_x·Ŝ_y` does too. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) :
    Commute (fermionStaggeredCasimirOp N A) (fermionTotalSpinZ N) :=
  fermionStaggeredCasimirOp_commute_fermionTotalSpinZ N A

/-- **`[Ô², Ŝ⁺_tot] = 0`.** Each per-pair `fermionSpinDot x y` commutes with `Ŝ⁺_tot`
(`totalSpinPlus_commute_fermionSpinDot`, `TJSpinSymmetryRaising.lean:112`), so the signed double
sum `Ô²` does too. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) :
    Commute (fermionStaggeredCasimirOp N A) (fermionTotalSpinPlus N) :=
  fermionStaggeredCasimirOp_commute_fermionTotalSpinPlus N A

/-- **`[Ô², Ŝ⁻_tot] = 0`.** Derived from `[Ô², Ŝ⁺_tot] = 0` by conjugate transposes, using
`(Ŝ⁺_tot)ᴴ = Ŝ⁻_tot` (`fermionTotalSpinPlus_conjTranspose`) and the Hermiticity of `Ô²`
(`fermionStaggeredCasimirOp_isHermitian`, `LiebFerrimagnetismStaggeredAlgebra.lean:148`) —
mirroring `fermionTotalSpinMinus_commute_symmetricRepulsiveHubbardHamiltonian`
(`LiebRepulsiveSU2Invariance.lean:145`). -/
example (N : ℕ) (A : Finset (Fin (N + 1))) :
    Commute (fermionStaggeredCasimirOp N A) (fermionTotalSpinMinus N) :=
  fermionStaggeredCasimirOp_commute_fermionTotalSpinMinus N A

end LatticeSystem.Tests.LiebFerrimagnetismSU2Invariance
