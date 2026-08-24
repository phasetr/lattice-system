import LatticeSystem.Math.MatrixAnalysis.LadderExpectationRatio

/-!
# §10.2.3 Theorem 10.6 — generic `SU(2)` ladder-expectation-ratio invariance (specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).)

Specification suite for
`LatticeSystem/Math/MatrixAnalysis/LadderExpectationRatio.lean`.
The `example`s pin down the exact signatures of the two generic lemmas stated for an arbitrary
`Matrix ι ι ℂ` pair `(Sp, Sm)`:

- `ladder_expectation_cross` — the cross identity
  `⟨Sm v, O (Sm v)⟩ = c • ⟨v, O v⟩` under `Smᴴ = Sp`, `Commute O Sp`, and the scalar action
  `(Sp * Sm) *ᵥ v = c • v`;
- `ladder_expectationRatioRe_invariant` — the same real Rayleigh-quotient invariance when
  `Sm *ᵥ v ≠ 0`.

These generalize the `SpinS`-specific pair `su2_expectation_ladder_cross` /
`su2_expectationRatioRe_ladder_invariant`
(`Quantum/SpinS/SU2ExpectationLadderInvariant.lean`) to any `Matrix ι ι ℂ`, so that the fermion
side (`fermionSpinMinus_expectationRatioRe_invariant`) and the retrofitted `SpinS` version can
both instantiate the same proof instead of duplicating it (this arc's PR-4 design). Mirrors the
specification style of `Tests/LiebFerrimagnetismStaggeredAlgebra.lean` /
`Tests/LiebFerrimagnetismTransverseCasimir.lean` / `Tests/LiebFerrimagnetismSU2Invariance.lean`,
so that the implementation cannot silently drift from the design's exact statements.
-/

namespace LatticeSystem.Tests.LadderExpectationRatio

open Matrix LatticeSystem.Math

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The cross identity: `ladder_expectation_cross` -/

/-- **Generic ladder-expectation cross identity.** For `O Sp Sm : Matrix ι ι ℂ` with
`Smᴴ = Sp` (`hadj`), `O` commuting with `Sp` (`hcomm`), and a joint eigenvector
`v` of `Sp * Sm` at scalar `c` (`hscal`), the complex expectation of `O` on the once-lowered
vector `Sm *ᵥ v` equals `c` times the expectation on `v`:
`⟨Sm v, O (Sm v)⟩ = c • ⟨v, O v⟩`, where `⟨a, b⟩ := star a ⬝ᵥ b`. -/
example (O Sp Sm : Matrix ι ι ℂ) (hadj : Smᴴ = Sp) (hcomm : Commute O Sp)
    {c : ℂ} {v : ι → ℂ} (hscal : (Sp * Sm).mulVec v = c • v) :
    star (Sm.mulVec v) ⬝ᵥ O.mulVec (Sm.mulVec v) = c • (star v ⬝ᵥ O.mulVec v) :=
  ladder_expectation_cross O Sp Sm hadj hcomm hscal

/-! ## 2. Real-expectation-ratio invariance: `ladder_expectationRatioRe_invariant` -/

/-- **Generic real-expectation-ratio ladder invariance.** With the same hypotheses as
`ladder_expectation_cross`, plus `Sm *ᵥ v ≠ 0`, the real Rayleigh quotient of `O` is unchanged
by the lowering step `v ↦ Sm *ᵥ v`:
`⟨Sm v, O (Sm v)⟩.re / ⟨Sm v, Sm v⟩.re = ⟨v, O v⟩.re / ⟨v, v⟩.re`. -/
example (O Sp Sm : Matrix ι ι ℂ) (hadj : Smᴴ = Sp) (hcomm : Commute O Sp)
    {c : ℂ} {v : ι → ℂ} (hscal : (Sp * Sm).mulVec v = c • v)
    (hne : Sm.mulVec v ≠ 0) :
    (star (Sm.mulVec v) ⬝ᵥ O.mulVec (Sm.mulVec v)).re /
        (star (Sm.mulVec v) ⬝ᵥ Sm.mulVec v).re =
      (star v ⬝ᵥ O.mulVec v).re / (star v ⬝ᵥ v).re :=
  ladder_expectationRatioRe_invariant O Sp Sm hadj hcomm hscal hne

end LatticeSystem.Tests.LadderExpectationRatio
