import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismLadderRatio

/-!
# §10.2.3 Theorem 10.6 — fermion ladder-expectation-ratio invariance (specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).)

Specification suite for
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebFerrimagnetismLadderRatio.lean`.
The `example` applies `fermionSpinMinus_expectationRatioRe_invariant` through *named* arguments,
so it pins the binder names as well as the argument types and order of
the fermion-level instantiation of the generic
`Math.MatrixAnalysis.LadderExpectationRatio.ladder_expectationRatioRe_invariant`
(`Math/MatrixAnalysis/LadderExpectationRatio.lean`) at `Sp := fermionTotalSpinPlus N`,
`Sm := fermionTotalSpinMinus N`, using `fermionTotalSpinMinus_conjTranspose`
(`(Ŝ⁻_tot)ᴴ = Ŝ⁺_tot`, `SpinTotHermitian.lean:35`) for the adjoint hypothesis and
`fermionTotalSpinPlus_mul_fermionTotalSpinMinus` (`Ŝ⁺_tot Ŝ⁻_tot = (Ŝ_tot)² − Ŝ³_tot(Ŝ³_tot − 1)`,
`WeakNagaokaTheorem.lean:45`) for the scalar action `c = γ − m² + m` on a joint `Ŝ³_tot` /
Casimir eigenvector, so that the implementation cannot silently drift from the design's exact
statement (this arc's PR-4 design). Mirrors the specification style of
`Tests/LiebFerrimagnetismSU2Invariance.lean`.
-/

namespace LatticeSystem.Tests.LiebFerrimagnetismLadderRatio

open Matrix LatticeSystem.Fermion LatticeSystem.Quantum

/-! ## The fermion-level real-expectation-ratio ladder invariance -/

/-- **Fermion `SU(2)`-invariant real-expectation-ratio ladder invariance.** Let
`O : ManyBodyOp (Fin (2N+2))` commute with the total raising operator
(`hOplus : Commute O Ŝ⁺_tot`), and let `v` be a joint `Ŝ³_tot` /
Casimir eigenvector (`Ŝ³_tot v = m • v`, `(Ŝ_tot)² v = γ • v`).  When the lowering is
non-vanishing (`Ŝ⁻_tot v ≠ 0`), the real Rayleigh quotient of `O` is preserved by the lowering:
`⟨Ŝ⁻v, O Ŝ⁻v⟩.re / ⟨Ŝ⁻v, Ŝ⁻v⟩.re = ⟨v, O v⟩.re / ⟨v, v⟩.re`, where `⟨a, b⟩ := star a ⬝ᵥ b`.
The `Ŝ⁻_tot` commutation is deliberately *not* a hypothesis: this pin fails if a future edit
re-adds it. -/
example (N : ℕ) (O : ManyBodyOp (Fin (2 * N + 2)))
    (hOplus : Commute O (fermionTotalSpinPlus N))
    {m γ : ℂ} {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hz : (fermionTotalSpinZ N).mulVec v = m • v)
    (hcas : (fermionTotalSpinSquared N).mulVec v = γ • v)
    (hne : (fermionTotalSpinMinus N).mulVec v ≠ 0) :
    (star ((fermionTotalSpinMinus N).mulVec v) ⬝ᵥ
          (O.mulVec ((fermionTotalSpinMinus N).mulVec v))).re /
        (star ((fermionTotalSpinMinus N).mulVec v) ⬝ᵥ
          ((fermionTotalSpinMinus N).mulVec v)).re =
      (star v ⬝ᵥ O.mulVec v).re / (star v ⬝ᵥ v).re :=
  fermionSpinMinus_expectationRatioRe_invariant (N := N) (O := O) (hOplus := hOplus) (m := m)
    (γ := γ) (v := v) (hz := hz) (hcas := hcas) (hne := hne)

end LatticeSystem.Tests.LiebFerrimagnetismLadderRatio
