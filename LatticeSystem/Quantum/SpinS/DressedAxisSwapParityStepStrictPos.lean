import LatticeSystem.Quantum.SpinS.DressedAxisSwapSingleIonStrictPos

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Strict positivity of the shifted PF matrix on every `ParityStepS` move

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

`ParityStepS G = RaiseLowerStepS G ∨ ParityBondStepS G ∨ SingleIonStepS`.  Under case (i) strict²
with `D > 0` (`−1 < λ.re < 1` real, real `D > 0` strict), every `ParityStepS` move gives a strict
positive shifted PF matrix entry:

* transverse (`RaiseLowerStepS`): #3792.
* bond parity (`ParityBondStepS`): #3793.
* single-ion (`SingleIonStepS`): #3794.

This is the unified `hB_step` of `Matrix.isIrreducible_iff_exists_pow_pos` in PR5 (parity-block
Perron–Frobenius irreducibility): combined with the reachability matrix-power lift (#3787) on the
full matrix and the block-power identity (#3789), it lifts parity-reachability to per-pair pow
positivity on the parity-block submatrix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Unified `ParityStepS` strict positivity of the shifted PF matrix** (case (i.2) strict, `D >
0`).
For a `ParityStepS` on `bipartiteCompleteGraphOf A` under `−1 < λ.re < 1` real, real `D > 0`
strict, the shifted matrix entry is strict positive. -/
theorem shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityStepS_bipartite
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    (c : ℝ)
    {σ τ : Λ → Fin (N + 1)} (hstep : ParityStepS (bipartiteCompleteGraphOf A) σ τ) :
    0 < shiftedDressedAxisSwappedReMatrix A J lam D N c τ σ := by
  rcases hstep with hRL | hPB | hSI
  · exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_raiseLowerStepS_bipartite
      A hJim hJnn hJpos hJself hJbip hlam hlb (le_of_lt hub) hDim (le_of_lt hDpos) c hRL
  · exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_parityBondStepS_bipartite
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim (le_of_lt hDpos) c hPB
  · exact shiftedDressedAxisSwappedReMatrix_apply_pos_of_singleIonStepS
      A hJself hDim hDpos c hSI

end LatticeSystem.Quantum
