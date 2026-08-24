import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismTransverseCasimir
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveFermionSpinCasimirBridge
import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionSiteSpin

/-!
# §10.2.3 Theorem 10.6 — transverse/Casimir identity and the weight band (specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).)

Specification suite for
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebFerrimagnetismTransverseCasimir.lean`.
`example`s pin down the exact signatures of
`sum_fermionSpinTransverse_eq_totalSpinSquared_sub_spinZ_sq`,
`fermionTotalSpinSquared_sub_spinZSq_posSemidef` and
`spinZ_sq_le_casimir_of_jointEigenvector`, mirroring PR-1's specification style
(`Tests/LiebFerrimagnetismStaggeredAlgebra.lean`), so that the implementation cannot silently
drift from the design's exact statements
(`.self-local/docs/theorem-10-6-design.md`, PR-2 section).

The closing sanity block is the cheapest falsifier of the root-selection step PR-5 relies on:
the Casimir equation `γ₀ = m(m + 1)` at `S₀ = 1/2` (`γ₀ = 3/4`) has two real roots, the physical
weight `m = 1/2` and the spurious top-weight root `m = -(S₀ + 1) = -3/2`; only the physical root
satisfies `m² ≤ γ₀`, which is exactly the content
`spinZ_sq_le_casimir_of_jointEigenvector` is meant to certify on an actual joint eigenvector.
-/

namespace LatticeSystem.Tests.LiebFerrimagnetismTransverseCasimir

open LatticeSystem.Fermion LatticeSystem.Quantum
open scoped BigOperators

/-! ## 1. The transverse/Casimir double-sum identity:
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

/-! ## 2. Positive-semidefiniteness of the transverse block -/

/-- **`(Ŝ_tot)² − (Ŝ³_tot)²` is positive semidefinite** (it is `Σ_x Σ_y Ŝ⊥_{xy}`,
`= ½(Ŝ⁺_totŜ⁻_tot + Ŝ⁻_totŜ⁺_tot)`, a sum of two `MᴴM` terms). This feeds the sign step
`ε_xε_y⟨Ŝ⊥_{xy}⟩ ≥ ⟨Ŝ⊥_{xy}⟩` of the design's Casimir step (§0.3). -/
example (N : ℕ) :
    (fermionTotalSpinSquared N - fermionTotalSpinZ N * fermionTotalSpinZ N).PosSemidef :=
  fermionTotalSpinSquared_sub_spinZSq_posSemidef N

/-! ## 3. The weight band `m² ≤ γ` on a joint eigenvector -/

/-- **Weight-band bound.**  On a nonzero joint eigenvector of `Ŝ³_tot` (eigenvalue `m`) and
`(Ŝ_tot)²` (eigenvalue `γ`), positive-semidefiniteness of `(Ŝ_tot)² − (Ŝ³_tot)²` forces
`m² ≤ γ`. This is exactly what excludes the spurious top-weight root `m = -(S₀ + 1)` of
`γ₀ = m(m + 1)` in PR-5's multiplet-grading argument. -/
example (N : ℕ) (m γ : ℝ) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (hv : v ≠ 0)
    (hz : (fermionTotalSpinZ N).mulVec v = (m : ℂ) • v)
    (hs : (fermionTotalSpinSquared N).mulVec v = (γ : ℂ) • v) :
    m ^ 2 ≤ γ :=
  spinZ_sq_le_casimir_of_jointEigenvector N m γ v hv hz hs

/-! ## 4. Root-selection sanity check (`S₀ = 1/2`, `γ₀ = 3/4`) -/

/-- **Physical root satisfies the band.** At spin `S₀ = 1/2` the Casimir value is
`γ₀ = S₀(S₀ + 1) = 3/4`, and the physical weight `m = S₀ = 1/2` obeys `m² ≤ γ₀`. -/
example : (1 / 2 : ℝ) ^ 2 ≤ (3 / 4 : ℝ) := by norm_num

/-- **Spurious root fails the band.** The other root of `γ₀ = m(m + 1)` at `γ₀ = 3/4` is the
top-weight companion `m = -(S₀ + 1) = -3/2`; it violates `m² ≤ γ₀`, so
`spinZ_sq_le_casimir_of_jointEigenvector` correctly excludes it. -/
example : ¬ (-3 / 2 : ℝ) ^ 2 ≤ (3 / 4 : ℝ) := by norm_num

end LatticeSystem.Tests.LiebFerrimagnetismTransverseCasimir
