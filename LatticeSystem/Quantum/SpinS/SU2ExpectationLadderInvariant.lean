import LatticeSystem.Quantum.SpinS.Theorem23TotalLoweringNonvanishing
import LatticeSystem.Math.MatrixAnalysis.LadderExpectationRatio

/-!
# SU(2)-invariant operator expectations are total-ladder invariant
(Issue #4604, universal-form transfer of Tasaki Theorem 4.4, ingredient (b))

For an operator `O : ManyBodyOpS V N` that is SU(2)-invariant — i.e. it commutes
with the total raising and lowering operators `Ŝ⁺_tot` and `Ŝ⁻_tot` — and a joint
`Ŝ³_tot` / Casimir `(Ŝ_tot)²` eigenvector `v` (with eigenvalues `m` and `γ`), the
complex expectation of `O` along the once-lowered vector `Ŝ⁻_tot v` scales by the
*same* real factor `c = γ − m² + m` as the squared norm:

  `⟨Ŝ⁻v, O (Ŝ⁻v)⟩ = (γ − m² + m) · ⟨v, O v⟩`,   `‖Ŝ⁻v‖² = (γ − m² + m) · ‖v‖²`.

The first is the *cross identity* `su2_expectation_ladder_cross`; the second is the
existing ladder-norm identity (`totalSpinSOpMinus_mulVec_normSq_eq`).  Dividing the
two yields the *real expectation ratio* invariance
`su2_expectationRatioRe_ladder_invariant`: the real Rayleigh quotient
`⟨v, O v⟩.re / ‖v‖²` is unchanged when `v` is lowered by `Ŝ⁻_tot` (when the
lowering is non-vanishing, so `c ≠ 0`).

Both are the spin-`S` specialisation of the model-agnostic pair
`ladder_expectation_cross` / `ladder_expectationRatioRe_invariant`
(`Math/MatrixAnalysis/LadderExpectationRatio.lean`) at `Sp := Ŝ⁺_tot`, `Sm := Ŝ⁻_tot`.
That generic pair needs exactly three inputs, supplied here by:
- `totalSpinSOpMinus_conjTranspose` for the adjoint hypothesis `(Ŝ⁻_tot)ᴴ = Ŝ⁺_tot`;
- the SU(2)-invariance hypothesis `Commute O Ŝ⁺_tot`;
- `totalSpinSOpPlus_mul_totalSpinSOpMinus_mulVec_eq` for the scalar action of
  `Ŝ⁺_tot Ŝ⁻_tot` on the joint eigenvector, whose eigenvalue `γ − m² + m` comes from
  `Ŝ⁺ Ŝ⁻ = (Ŝ_tot)² − (Ŝ³_tot)² + Ŝ³_tot`
  (`totalSpinSOpPlus_mul_totalSpinSOpMinus_eq_casimir_minus_z_sq_add_z`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §4 (Theorem 4.4) and §2.5 (Lieb–Mattis / SU(2) ladder structure).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Scalar action of `Ŝ⁺_tot Ŝ⁻_tot` on a joint eigenvector.** If
`Ŝ³_tot v = m • v` and `(Ŝ_tot)² v = γ • v`, then
`(Ŝ⁺_tot Ŝ⁻_tot) *ᵥ v = (γ − m·m + m) • v`, the Casimir-rearrangement eigenvalue. -/
theorem totalSpinSOpPlus_mul_totalSpinSOpMinus_mulVec_eq
    {m γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec v = m • v)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v) :
    (totalSpinSOpPlus V N * totalSpinSOpMinus V N).mulVec v =
      (γ - m * m + m) • v := by
  rw [totalSpinSOpPlus_mul_totalSpinSOpMinus_eq_casimir_minus_z_sq_add_z]
  -- `(S² − S³S³ + S³) *ᵥ v`, expand the additive matrix structure.
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, hcas]
  -- `S³S³ *ᵥ v = S³ *ᵥ (S³ *ᵥ v) = m·m • v`.
  rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_smul, hz, smul_smul]
  -- now: `γ • v − (m*m) • v + m • v = (γ − m*m + m) • v`.
  module

/-- **SU(2)-invariant expectation cross identity (lowering step).** Let
`O : ManyBodyOpS V N` commute with both total ladder operators; for a joint
`Ŝ³_tot` / Casimir eigenvector `v` (`Ŝ³_tot v = m • v`, `(Ŝ_tot)² v = γ • v`),

  `⟨Ŝ⁻v, O (Ŝ⁻v)⟩ = (γ − m² + m) · ⟨v, O v⟩`,

i.e. the complex expectation of `O` on the once-lowered vector equals the
Casimir-rearrangement scalar `γ − m·m + m` times the expectation on `v`.  The
`Ŝ⁻_tot`-commutation belongs to the SU(2)-invariance package carried by the
callers, but the identity itself needs only the `Ŝ⁺_tot` one. -/
theorem su2_expectation_ladder_cross (O : ManyBodyOpS V N)
    (hOplus : Commute O (totalSpinSOpPlus V N))
    (_hOminus : Commute O (totalSpinSOpMinus V N))
    {m γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec v = m • v)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v) :
    star ((totalSpinSOpMinus V N).mulVec v) ⬝ᵥ
        (O.mulVec ((totalSpinSOpMinus V N).mulVec v)) =
      (γ - m * m + m) • (star v ⬝ᵥ O.mulVec v) :=
  LatticeSystem.Math.ladder_expectation_cross O (totalSpinSOpPlus V N)
    (totalSpinSOpMinus V N) (totalSpinSOpMinus_conjTranspose V N) hOplus
    (totalSpinSOpPlus_mul_totalSpinSOpMinus_mulVec_eq hz hcas)

/-- **SU(2)-invariant real-expectation-ratio ladder invariance.** With the same
SU(2)-invariance and joint-eigenvector hypotheses, if the lowering is non-vanishing
(`Ŝ⁻_tot v ≠ 0`), the real Rayleigh quotient of `O` is preserved by the lowering:

  `⟨Ŝ⁻v, O Ŝ⁻v⟩.re / ⟨Ŝ⁻v, Ŝ⁻v⟩.re = ⟨v, O v⟩.re / ⟨v, v⟩.re`.

Both numerator and denominator scale by the common real factor `(γ − m² + m).re`
(the squared lowering-norm ratio, positive when `Ŝ⁻_tot v ≠ 0`), so the quotient is
unchanged.  Here `⟨a, b⟩ := star a ⬝ᵥ b`. -/
theorem su2_expectationRatioRe_ladder_invariant (O : ManyBodyOpS V N)
    (hOplus : Commute O (totalSpinSOpPlus V N))
    (_hOminus : Commute O (totalSpinSOpMinus V N))
    {m γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec v = m • v)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v)
    (hne : (totalSpinSOpMinus V N).mulVec v ≠ 0) :
    (star ((totalSpinSOpMinus V N).mulVec v) ⬝ᵥ
          (O.mulVec ((totalSpinSOpMinus V N).mulVec v))).re /
        (star ((totalSpinSOpMinus V N).mulVec v) ⬝ᵥ
          ((totalSpinSOpMinus V N).mulVec v)).re =
      (star v ⬝ᵥ O.mulVec v).re / (star v ⬝ᵥ v).re :=
  LatticeSystem.Math.ladder_expectationRatioRe_invariant O (totalSpinSOpPlus V N)
    (totalSpinSOpMinus V N) (totalSpinSOpMinus_conjTranspose V N) hOplus
    (totalSpinSOpPlus_mul_totalSpinSOpMinus_mulVec_eq hz hcas) hne

end LatticeSystem.Quantum
