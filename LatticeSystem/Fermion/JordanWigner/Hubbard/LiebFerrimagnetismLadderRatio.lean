import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinTotHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheorem
import LatticeSystem.Math.MatrixAnalysis.LadderExpectationRatio

/-!
# Ladder invariance of fermionic real expectation ratios (Tasaki §10.2.3)

Hubbard-fermion instance of the model-agnostic ladder-ratio lemma
`ladder_expectationRatioRe_invariant` (`Math/MatrixAnalysis/LadderExpectationRatio.lean`) at
`Sp := Ŝ⁺_tot`, `Sm := Ŝ⁻_tot`.  For an operator `O` commuting with `Ŝ⁺_tot` and a joint
`Ŝ³_tot` / Casimir eigenvector `v` (`Ŝ³_tot v = m v`, `(Ŝ_tot)² v = γ v`) with `Ŝ⁻_tot v ≠ 0`,
the real Rayleigh quotient of `O` is unchanged by the lowering step `v ↦ Ŝ⁻_tot v`:

  `⟨Ŝ⁻v, O Ŝ⁻v⟩.re / ‖Ŝ⁻v‖² = ⟨v, O v⟩.re / ‖v‖²`,   `⟨a, b⟩ := star a ⬝ᵥ b`.

The generic lemma's three inputs are supplied by `fermionTotalSpinMinus_conjTranspose`
(`(Ŝ⁻_tot)ᴴ = Ŝ⁺_tot`), the SU(2)-invariance hypothesis `Commute O Ŝ⁺_tot`, and the scalar action
of `Ŝ⁺_tot Ŝ⁻_tot` obtained from the Casimir rearrangement
`fermionTotalSpinPlus_mul_fermionTotalSpinMinus`
(`Ŝ⁺_tot Ŝ⁻_tot = (Ŝ_tot)² − Ŝ³_tot (Ŝ³_tot − 1)`), whose eigenvalue on `v` is `γ − m² + m`.

This is the ladder ingredient of Theorem 10.6: the ferrimagnetic long-range-order ratio computed
on one member of the ground multiplet is the same on every member of its lowering tower.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **Fermionic ladder invariance of the real expectation ratio.** For `O` commuting with
`Ŝ⁺_tot` and a joint `Ŝ³_tot` / Casimir eigenvector `v` with `Ŝ⁻_tot v ≠ 0`,
`⟨Ŝ⁻v, O Ŝ⁻v⟩.re / ⟨Ŝ⁻v, Ŝ⁻v⟩.re = ⟨v, O v⟩.re / ⟨v, v⟩.re` (with `⟨a, b⟩ := star a ⬝ᵥ b`).
The `Ŝ⁻_tot`-commutation hypothesis is part of the SU(2)-invariance package carried by the
callers, but the ratio identity needs only the `Ŝ⁺_tot` one. -/
theorem fermionSpinMinus_expectationRatioRe_invariant (N : ℕ) (O : ManyBodyOp (Fin (2 * N + 2)))
    (hOplus : Commute O (fermionTotalSpinPlus N))
    (_hOminus : Commute O (fermionTotalSpinMinus N))
    {m γ : ℂ} {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hz : (fermionTotalSpinZ N).mulVec v = m • v)
    (hcas : (fermionTotalSpinSquared N).mulVec v = γ • v)
    (hne : (fermionTotalSpinMinus N).mulVec v ≠ 0) :
    (star ((fermionTotalSpinMinus N).mulVec v) ⬝ᵥ
          (O.mulVec ((fermionTotalSpinMinus N).mulVec v))).re /
        (star ((fermionTotalSpinMinus N).mulVec v) ⬝ᵥ
          ((fermionTotalSpinMinus N).mulVec v)).re =
      (star v ⬝ᵥ O.mulVec v).re / (star v ⬝ᵥ v).re := by
  -- `Ŝ⁺_tot Ŝ⁻_tot = (Ŝ_tot)² − Ŝ³_tot (Ŝ³_tot − 1)` acts on `v` as `γ − m² + m`.
  have hscal : (fermionTotalSpinPlus N * fermionTotalSpinMinus N).mulVec v =
      (γ - m * m + m) • v := by
    rw [fermionTotalSpinPlus_mul_fermionTotalSpinMinus, Matrix.sub_mulVec, hcas,
      ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hz, Matrix.mulVec_sub,
      Matrix.mulVec_smul, hz]
    module
  exact LatticeSystem.Math.ladder_expectationRatioRe_invariant O (fermionTotalSpinPlus N)
    (fermionTotalSpinMinus N) (fermionTotalSpinMinus_conjTranspose N) hOplus hscal hne

end LatticeSystem.Fermion
