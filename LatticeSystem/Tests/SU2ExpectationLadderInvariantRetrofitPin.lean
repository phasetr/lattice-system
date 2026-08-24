import LatticeSystem.Quantum.SpinS.SU2ExpectationLadderInvariant

/-!
# §10.2.3 Theorem 10.6 — `SpinS` retrofit statement pin (regression specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).)

This arc's PR-4 retrofits `su2_expectation_ladder_cross`
(`Quantum/SpinS/SU2ExpectationLadderInvariant.lean:69`) and
`su2_expectationRatioRe_ladder_invariant` (`Quantum/SpinS/SU2ExpectationLadderInvariant.lean:102`)
onto the new generic `Math.MatrixAnalysis.LadderExpectationRatio` lemmas
(`Tests/LadderExpectationRatio.lean`), keeping both statements **byte-identical** and turning only
their proofs into instantiations of the generic lemma (approved retrofit scope; see this arc's
PR-4 design). The single downstream consumer,
`su2_expectationRatioRe_ladder_iterate_invariant`
(`Quantum/SpinS/SU2ExpectationLadderIterated.lean:76`), must keep compiling unchanged against
these exact signatures.

The two `example`s below reproduce the exact current signatures (as of the pre-retrofit state)
so that any accidental change to argument order, binder names/types, or the conclusion during the
retrofit is caught at compile time.
-/

namespace LatticeSystem.Tests.SU2ExpectationLadderInvariantRetrofitPin

open Matrix LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Pin: `su2_expectation_ladder_cross` (`SU2ExpectationLadderInvariant.lean:69`) -/

/-- **Statement pin.** The retrofit must not change this signature: `O : ManyBodyOpS V N`,
`hOplus : Commute O Ŝ⁺_tot`, `_hOminus : Commute O Ŝ⁻_tot` (unused post-retrofit, kept for the
call site at `su2_expectationRatioRe_ladder_invariant`), joint eigenvector data
`hz : Ŝ³_tot v = m • v`, `hcas : (Ŝ_tot)² v = γ • v`, concluding the cross identity
`⟨Ŝ⁻v, O Ŝ⁻v⟩ = (γ − m² + m) • ⟨v, O v⟩`. -/
example (O : ManyBodyOpS V N)
    (hOplus : Commute O (totalSpinSOpPlus V N))
    (_hOminus : Commute O (totalSpinSOpMinus V N))
    {m γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec v = m • v)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v) :
    star ((totalSpinSOpMinus V N).mulVec v) ⬝ᵥ
        (O.mulVec ((totalSpinSOpMinus V N).mulVec v)) =
      (γ - m * m + m) • (star v ⬝ᵥ O.mulVec v) :=
  su2_expectation_ladder_cross O hOplus _hOminus hz hcas

/-! ## Pin: `su2_expectationRatioRe_ladder_invariant` (`SU2ExpectationLadderInvariant.lean:102`) -/

/-- **Statement pin.** The retrofit must not change this signature: same hypothesis bundle as
above (`hOminus` now genuinely used) plus `hne : Ŝ⁻_tot v ≠ 0`, concluding the real
Rayleigh-quotient invariance under the lowering step. -/
example (O : ManyBodyOpS V N)
    (hOplus : Commute O (totalSpinSOpPlus V N))
    (hOminus : Commute O (totalSpinSOpMinus V N))
    {m γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec v = m • v)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v)
    (hne : (totalSpinSOpMinus V N).mulVec v ≠ 0) :
    (star ((totalSpinSOpMinus V N).mulVec v) ⬝ᵥ
          (O.mulVec ((totalSpinSOpMinus V N).mulVec v))).re /
        (star ((totalSpinSOpMinus V N).mulVec v) ⬝ᵥ
          ((totalSpinSOpMinus V N).mulVec v)).re =
      (star v ⬝ᵥ O.mulVec v).re / (star v ⬝ᵥ v).re :=
  su2_expectationRatioRe_ladder_invariant O hOplus hOminus hz hcas hne

end LatticeSystem.Tests.SU2ExpectationLadderInvariantRetrofitPin
