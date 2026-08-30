import LatticeSystem.Math.MatrixAnalysis.LadderExpectationRatio
import Mathlib.LinearAlgebra.Matrix.Notation

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

Neither `example` assumes `DecidableEq ι`, pinning that the generic lemmas stay
`DecidableEq`-free (the `1 : Matrix ι ι ℂ` used inside the second proof is `classical`).
Section 3 adds the numerical counterpart: the two lemmas are instantiated on an explicit `2 × 2`
spin-`½` `su(2)` toy and the resulting expectation and Rayleigh quotient are checked against the
hand-computed values, so a drift in either conclusion (a wrong scalar, a swapped ladder, a
misplaced `star`) is caught by an actual computation rather than by a tautological signature pin.

These generalize the `SpinS`-specific pair `su2_expectation_ladder_cross` /
`su2_expectationRatioRe_ladder_invariant` (`Quantum/SpinS/SU2ExpectationLadderInvariant.lean`) to
any `Matrix ι ι ℂ`, so that the fermion side (`fermionSpinMinus_expectationRatioRe_invariant`) and
the retrofitted `SpinS` version can both instantiate the same proof instead of duplicating it.
Mirrors the specification style of `Tests/LiebFerrimagnetismStaggeredAlgebra.lean` /
`Tests/LiebFerrimagnetismTransverseCasimir.lean` / `Tests/LiebFerrimagnetismSU2Invariance.lean`,
so that the implementation cannot silently drift from the statements pinned here.
-/

namespace LatticeSystem.Tests.LadderExpectationRatio

open Matrix LatticeSystem.Math

variable {ι : Type*} [Fintype ι]

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

/-! ## 3. Numerical regression witness: the `2 × 2` spin-`½` `su(2)` toy

`Sp = 2σ⁺`, `Sm = 2σ⁻`, `v = e₀` (the highest-weight state), `O = a • 1 + b • Sp`.  Then
`Sm *ᵥ e₀ = 2e₁`, `(Sp * Sm) *ᵥ e₀ = 4 • e₀` (so `c = 4`), `⟨e₀, O e₀⟩ = a` and `‖e₀‖² = 1`, so
the two lemmas must return `⟨Sm e₀, O (Sm e₀)⟩ = 4a` and `Re⟨Sm e₀, O (Sm e₀)⟩/‖Sm e₀‖² = Re a`.
-/

/-- Toy raising generator `S⁺ = 2σ⁺` on the spin-`½` doublet `ℂ² ≃ (Fin 2 → ℂ)`. -/
private def toySpinPlus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 2; 0, 0]

/-- Toy lowering generator `S⁻ = 2σ⁻`, the adjoint of `toySpinPlus`. -/
private def toySpinMinus : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 2, 0]

/-- Toy observable `O = a • 1 + b • S⁺`, the generic operator commuting with `S⁺`. -/
private def toyObs (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := a • 1 + b • toySpinPlus

/-- Toy highest-weight vector `e₀` (the `S³ = +½` state). -/
private def toyVec : Fin 2 → ℂ := ![1, 0]

/-- Adjoint hypothesis for the toy pair: `(S⁻)ᴴ = S⁺`. -/
private theorem toySpinMinus_conjTranspose : toySpinMinusᴴ = toySpinPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [toySpinMinus, toySpinPlus, Matrix.conjTranspose_apply]

/-- Commutation hypothesis for the toy pair: `O = a • 1 + b • S⁺` commutes with `S⁺`. -/
private theorem toyObs_commute (a b : ℂ) : Commute (toyObs a b) toySpinPlus :=
  ((Commute.one_left toySpinPlus).smul_left a).add_left
    ((Commute.refl toySpinPlus).smul_left b)

/-- Scalar-action hypothesis for the toy pair: `(S⁺S⁻) *ᵥ e₀ = 4 • e₀`, i.e. `c = 4`. -/
private theorem toySpinPlus_mul_toySpinMinus_mulVec :
    (toySpinPlus * toySpinMinus).mulVec toyVec = (4 : ℂ) • toyVec := by
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two, toySpinPlus,
      toySpinMinus, toyVec]

/-- The toy lowering step is the explicit vector `S⁻ *ᵥ e₀ = 2e₁`. -/
private theorem toySpinMinus_mulVec_toyVec : toySpinMinus.mulVec toyVec = ![0, 2] := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, toySpinMinus, toyVec]

/-- Non-vanishing hypothesis for the toy pair: `S⁻ *ᵥ e₀ = 2e₁ ≠ 0`. -/
private theorem toySpinMinus_mulVec_toyVec_ne_zero : toySpinMinus.mulVec toyVec ≠ 0 := by
  intro h
  have h1 : (![0, 2] : Fin 2 → ℂ) 1 = (0 : Fin 2 → ℂ) 1 := by
    rw [← toySpinMinus_mulVec_toyVec, h]
  norm_num at h1

/-- **Numerical witness for `ladder_expectation_cross`.** On the toy data the cross identity must
produce the hand-computed value `⟨S⁻e₀, O (S⁻e₀)⟩ = 4a` (`= c · ⟨e₀, O e₀⟩` with `c = 4`,
`⟨e₀, O e₀⟩ = a`). -/
example (a b : ℂ) :
    star (toySpinMinus.mulVec toyVec) ⬝ᵥ (toyObs a b).mulVec (toySpinMinus.mulVec toyVec) =
      4 * a := by
  rw [ladder_expectation_cross (toyObs a b) toySpinPlus toySpinMinus toySpinMinus_conjTranspose
    (toyObs_commute a b) toySpinPlus_mul_toySpinMinus_mulVec]
  simp [toyObs, toySpinPlus, toyVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Numerical witness for `ladder_expectationRatioRe_invariant`.** On the toy data the lowered
real Rayleigh quotient is `Re(4a)/4 = Re a`, the same as the quotient `Re a / 1` on `e₀`. -/
example (a b : ℂ) :
    (star (toySpinMinus.mulVec toyVec) ⬝ᵥ (toyObs a b).mulVec (toySpinMinus.mulVec toyVec)).re /
        (star (toySpinMinus.mulVec toyVec) ⬝ᵥ toySpinMinus.mulVec toyVec).re = a.re := by
  rw [ladder_expectationRatioRe_invariant (toyObs a b) toySpinPlus toySpinMinus
    toySpinMinus_conjTranspose (toyObs_commute a b) toySpinPlus_mul_toySpinMinus_mulVec
    toySpinMinus_mulVec_toyVec_ne_zero]
  simp [toyObs, toySpinPlus, toyVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end LatticeSystem.Tests.LadderExpectationRatio
