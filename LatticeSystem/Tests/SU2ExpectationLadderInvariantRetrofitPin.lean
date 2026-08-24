import LatticeSystem.Quantum.SpinS.SU2ExpectationLadderInvariant

/-!
# §10.2.3 Theorem 10.6 — `SpinS` retrofit statement pin (regression specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).)

This arc's PR-4 retrofits `su2_expectation_ladder_cross`
(`Quantum/SpinS/SU2ExpectationLadderInvariant.lean:71`) and
`su2_expectationRatioRe_ladder_invariant` (`Quantum/SpinS/SU2ExpectationLadderInvariant.lean:93`)
onto the new generic `Math.MatrixAnalysis.LadderExpectationRatio` lemmas
(`Tests/LadderExpectationRatio.lean`), keeping both **types** unchanged and turning only their
proofs into instantiations of the generic lemma (approved retrofit scope; see this arc's PR-4
design). The one binder-level change is a rename: since the generic lemma needs only
`Commute O Ŝ⁺_tot`, the lowering-commutation binder of
`su2_expectationRatioRe_ladder_invariant` became unused and is now spelled `_hOminus` (as
`su2_expectation_ladder_cross` already spelled it), which `warningAsError = true` requires. The
single downstream consumer, `su2_expectationRatioRe_ladder_iterate_invariant`
(`Quantum/SpinS/SU2ExpectationLadderIterated.lean:76`), passes its arguments positionally and so
keeps compiling unchanged against these signatures.

The two `example`s below apply the theorems through *named* arguments, so argument order, binder
names, binder types and the conclusion are all pinned at compile time; a further rename (or an
added/dropped hypothesis) breaks this file.
-/

namespace LatticeSystem.Tests.SU2ExpectationLadderInvariantRetrofitPin

open Matrix LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Pin: `su2_expectation_ladder_cross` (`SU2ExpectationLadderInvariant.lean:71`) -/

/-- **Signature pin.** The retrofit must not change this signature: `O : ManyBodyOpS V N`,
`hOplus : Commute O Ŝ⁺_tot`, `_hOminus : Commute O Ŝ⁻_tot` (unused, kept because the callers carry
the whole SU(2)-invariance package), joint eigenvector data `hz : Ŝ³_tot v = m • v`,
`hcas : (Ŝ_tot)² v = γ • v`, concluding the cross identity
`⟨Ŝ⁻v, O Ŝ⁻v⟩ = (γ − m² + m) • ⟨v, O v⟩`. -/
example (O : ManyBodyOpS V N)
    (hOplus : Commute O (totalSpinSOpPlus V N))
    (hOminus : Commute O (totalSpinSOpMinus V N))
    {m γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec v = m • v)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v) :
    star ((totalSpinSOpMinus V N).mulVec v) ⬝ᵥ
        (O.mulVec ((totalSpinSOpMinus V N).mulVec v)) =
      (γ - m * m + m) • (star v ⬝ᵥ O.mulVec v) :=
  su2_expectation_ladder_cross (O := O) (hOplus := hOplus) (_hOminus := hOminus) (m := m) (γ := γ)
    (v := v) (hz := hz) (hcas := hcas)

/-! ## Pin: `su2_expectationRatioRe_ladder_invariant` (`SU2ExpectationLadderInvariant.lean:93`) -/

/-- **Signature pin.** The retrofit must not change this signature: same hypothesis bundle as
above (the lowering-commutation binder is likewise spelled `_hOminus` post-retrofit) plus
`hne : Ŝ⁻_tot v ≠ 0`, concluding the real Rayleigh-quotient invariance under the lowering step. -/
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
  su2_expectationRatioRe_ladder_invariant (O := O) (hOplus := hOplus) (_hOminus := hOminus)
    (m := m) (γ := γ) (v := v) (hz := hz) (hcas := hcas) (hne := hne)

end LatticeSystem.Tests.SU2ExpectationLadderInvariantRetrofitPin
