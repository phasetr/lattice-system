import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensity
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityTrial
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityRothCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityRoth
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandEigenbasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUTrial
import LatticeSystem.Math.MatrixAnalysis.RowSumEigenvalueBound
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix

/-!
# Test coverage for Theorem 11.4 PR-6 (Roth's variational bound)

Continues the numbering of `LatticeSystem.Tests.HubbardImpossibilityLowDensity` (which ends at
Red 31) in a sibling module, per the PR-6 design (`.self-local/docs/theorem-11-4-pr6-design.md`
§5/§8 decision 3): the existing module is already at 714 lines, past the 700-line review trigger.

These tests pin the three new PR-6 modules before they exist:

* `LatticeSystem.Math.MatrixAnalysis.RowSumEigenvalueBound` — the generic Gershgorin row-sum
  corollary `norm_le_of_mulVec_eq_smul_of_rowSum_le` (G1).
* `LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityRothCore` — the
  number-sandwich identity `fermionMultiNumber_mul_hubbardKineticSpin_mul_self` (R6) and its
  supporting lemmas (R1–R5, R7).
* `LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityRoth` — the Roth state
  `hubbardLowDensityRothState` (V0) and the capstone Rayleigh bound
  `rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le` (V7), with the intermediate
  double-occupancy weight `dotProduct_star_hubbardOnSiteInteraction_hubbardLowDensityTrialState_re`
  (V3) and positivity `dotProduct_star_self_hubbardLowDensityRothState_pos` (V6).

None of these three modules exist yet in this tree, so every test below fails to elaborate — this
*is* the Red evidence for PR-6 (design §5: "`sorry` is a build error here, so the Red phase is
'statement exists, referenced name does not'").

- **Red 32 (primary consumption, Method D)**: the capstone V7 at `M := 1`, `SUp := ∅`, `t := 0`,
  `v := ![1/√2, 1/√2]` (so `hmod` holds with `e₁ := 0`, `K := 0`, `hhalf` holds vacuously): the
  bound collapses to `rayleighOnVec Ĥ Ψ̃ ≤ 0`. Fails hardest before the implementation exists.
- **Red 33 (`U`-independence, the theorem's headline)**: V7 instantiated at two distinct `U`
  values on the same fixture produces the *same* numeral bound — Theorem 11.4 holds for every
  `U`, and a proof that accidentally retained a `U`-dependent term would fail this test.
- **Red 34 / 34b (V3 pinned, the `1/Ns` factor)**: the double-occupancy weight at `M := 1`,
  `SUp := {0}` (ratio `1/2`) and `M := 2`, `SUp := {0, 1}` (ratio `2/3`), pinning
  `SUp.card / (M + 1)` as a genuine ratio rather than a coincidence at one fixture (the PR-5 Red
  20/21 discipline).
- **Red 35 (R6 pinned at a diagonal `t`)**: for `t` diagonal the correction term of the number
  sandwich vanishes, so `n̂ Ĥ^σ n̂ = n̂ Ĥ^σ`. Guards a sign slip or a dropped diagonal term.
- **Red 36 (R6 spin-tag guard)**: the sandwich at `σ := 0` versus `σ := 1` on the same `t` — both
  hold, and the statement's `spinfulIndex M x σ` must track `σ` (mirrors PR-4's Red 19).
- **Red 37 (G1 sharpness)**: without the row-sum hypothesis `hK`, the conclusion `‖lam‖ ≤ K` is
  false: on `Fin 1`, `t := ![![2]]`, `lam := 2`, `K := 1` — the row sum is `2 > 1`. Standalone,
  mirrors PR-5 Red 22 / PR-5b Red 30.
- **Red 38 (V6 non-vacuity)**: `0 < ‖Ψ̃‖²` at a concrete configuration — the Roth projection does
  not annihilate the trial state, guarding against a "bound proved because both sides are 0"
  degeneracy in Red 32.
- **Red 39 (`hhalf` sharpness)**: without `2 * SUp.card ≤ M + 1` the constant `8` is not enough;
  exhibited as a standalone real-inequality failure at `ρ := SUp.card / (M + 1) → 1`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.4, eqs. (11.1.9)/(11.1.10), p. 376; Tasaki, Prog. Theor. Phys. **99**
(1998) 489, Theorem 3.3, Appendix F, eqs. (F.1)–(F.13), pp. 545–546.
-/

namespace LatticeSystem.Tests.HubbardImpossibilityLowDensityRoth

open LatticeSystem.Fermion
open LatticeSystem.Quantum

open scoped BigOperators

/-- Fixture: the zero hopping matrix on `Fin 2` is Hermitian, its eigenvalues are all `0`. -/
private noncomputable def hT0 : (0 : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
  unfold Matrix.IsHermitian
  simp

/-- **Red 32 (primary consumption, Method D).** At `M := 1`, `SUp := ∅`, `t := 0`,
`v := ![1 / Real.sqrt 2, 1 / Real.sqrt 2]` (`hmod` holds since `‖v x‖ ^ 2 = 1 / 2`), `e₁ := 0`
(`t.mulVec v = 0 = (0 : ℂ) • v`), `K := 0` (the zero matrix's row sums are `0`), `hhalf` holds
vacuously (`SUp.card = 0`): the capstone bound collapses to `rayleighOnVec Ĥ Ψ̃ ≤ 0`. This is the
single hardest consumption test — every binder of V7 is exercised at once. -/
example (U : ℝ) :
    rayleighOnVec (hubbardHamiltonian 1 (0 : Matrix (Fin 2) (Fin 2) ℂ) (U : ℂ))
        (hubbardLowDensityRothState (eigenbasisAsBasis hT0) (∅ : Finset (Fin 2))
          (v := ![1 / Real.sqrt 2, 1 / Real.sqrt 2]))
      ≤ 0 := by
  have hv : (0 : Matrix (Fin 2) (Fin 2) ℂ).mulVec ![1 / Real.sqrt 2, 1 / Real.sqrt 2]
      = ((0 : ℝ) : ℂ) • ![1 / Real.sqrt 2, 1 / Real.sqrt 2] := by
    simp [Matrix.zero_mulVec]
  have hmod : ∀ x : Fin 2, ‖(![1 / Real.sqrt 2, 1 / Real.sqrt 2] : Fin 2 → ℂ) x‖ ^ 2
      = 1 / ((1 : ℝ) + 1) := by
    intro x
    fin_cases x <;>
      simp [Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_nonneg, Real.sq_sqrt,
        Real.sqrt_nonneg]
  have hK : ∀ x : Fin 2, ∑ y : Fin 2, ‖(0 : Matrix (Fin 2) (Fin 2) ℂ) x y‖ ≤ (0 : ℝ) := by
    intro x; simp
  have hhalf : 2 * ((∅ : Finset (Fin 2)).card : ℝ) ≤ (1 : ℝ) + 1 := by simp
  have hbound := rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le
    hT0 (∅ : Finset (Fin 2)) hv hmod hK hhalf U
  simpa [occupiedEigenEnergy] using hbound

/-- **Red 33 (`U`-independence, the theorem's headline).** V7 at two distinct `U` values on the
`Red 32` fixture produces the *literally same* numeral bound `0` — Theorem 11.4 holds for every
`U ≥ 0`, and a proof that accidentally kept a `U`-dependent term would fail this test. -/
example :
    (rayleighOnVec (hubbardHamiltonian 1 (0 : Matrix (Fin 2) (Fin 2) ℂ) ((0 : ℝ) : ℂ))
        (hubbardLowDensityRothState (eigenbasisAsBasis hT0) (∅ : Finset (Fin 2))
          (v := ![1 / Real.sqrt 2, 1 / Real.sqrt 2])) ≤ 0)
    ∧
    (rayleighOnVec (hubbardHamiltonian 1 (0 : Matrix (Fin 2) (Fin 2) ℂ) ((5 : ℝ) : ℂ))
        (hubbardLowDensityRothState (eigenbasisAsBasis hT0) (∅ : Finset (Fin 2))
          (v := ![1 / Real.sqrt 2, 1 / Real.sqrt 2])) ≤ 0) := by
  have hv : (0 : Matrix (Fin 2) (Fin 2) ℂ).mulVec ![1 / Real.sqrt 2, 1 / Real.sqrt 2]
      = ((0 : ℝ) : ℂ) • ![1 / Real.sqrt 2, 1 / Real.sqrt 2] := by
    simp [Matrix.zero_mulVec]
  have hmod : ∀ x : Fin 2, ‖(![1 / Real.sqrt 2, 1 / Real.sqrt 2] : Fin 2 → ℂ) x‖ ^ 2
      = 1 / ((1 : ℝ) + 1) := by
    intro x
    fin_cases x <;>
      simp [Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_nonneg, Real.sq_sqrt,
        Real.sqrt_nonneg]
  have hK : ∀ x : Fin 2, ∑ y : Fin 2, ‖(0 : Matrix (Fin 2) (Fin 2) ℂ) x y‖ ≤ (0 : ℝ) := by
    intro x; simp
  have hhalf : 2 * ((∅ : Finset (Fin 2)).card : ℝ) ≤ (1 : ℝ) + 1 := by simp
  constructor
  · simpa [occupiedEigenEnergy] using
      rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le
        hT0 (∅ : Finset (Fin 2)) hv hmod hK hhalf (0 : ℝ)
  · simpa [occupiedEigenEnergy] using
      rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le
        hT0 (∅ : Finset (Fin 2)) hv hmod hK hhalf (5 : ℝ)

/-- Fixture: the zero hopping matrix on `Fin 3` (`M := 2`) is Hermitian. -/
private noncomputable def hT0' : (0 : Matrix (Fin 3) (Fin 3) ℂ).IsHermitian := by
  unfold Matrix.IsHermitian
  simp

/-- **Red 34 (V3 pinned, the `1/Ns` factor at `M := 1`).** With `SUp := {0}`
(`SUp.card = 1`, `M + 1 = 2`) the double-occupancy weight is `D = (1/2) · P`, `P := ⟨Φ↑, Φ↑⟩.re`. A
lost `1/Ns` factor or an `Ne` vs. `Ne − 1` slip breaks exactly this ratio. -/
example {v : Fin 2 → ℂ} (hmod : ∀ x, ‖v x‖ ^ 2 = 1 / ((1 : ℝ) + 1)) :
    (star (hubbardLowDensityTrialState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) v) ⬝ᵥ
        (hubbardOnSiteInteraction 1 1).mulVec
          (hubbardLowDensityTrialState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) v)).re
      = (1 / 2 : ℝ) *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) ∅) ⬝ᵥ
            spinfulGeneralBasisState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) ∅).re := by
  have h := dotProduct_star_hubbardOnSiteInteraction_hubbardLowDensityTrialState_re
    hT0 ({0} : Finset (Fin 2)) hmod
  simpa using h

/-- **Red 34b (V3 pinned at `M := 2`).** With `SUp := {0, 1}` (`SUp.card = 2`, `M + 1 = 3`) the
ratio is `2/3`, run at a second fixture so `SUp.card / (M + 1)` is pinned as a genuine shape rather
than a coincidence at Red 34's `1/2`. -/
example {v : Fin 3 → ℂ} (hmod : ∀ x, ‖v x‖ ^ 2 = 1 / ((2 : ℝ) + 1)) :
    (star (hubbardLowDensityTrialState (eigenbasisAsBasis hT0') ({0, 1} : Finset (Fin 3)) v) ⬝ᵥ
        (hubbardOnSiteInteraction 2 1).mulVec
          (hubbardLowDensityTrialState (eigenbasisAsBasis hT0') ({0, 1} : Finset (Fin 3)) v)).re
      = (2 / 3 : ℝ) *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT0') ({0, 1} : Finset (Fin 3)) ∅) ⬝ᵥ
            spinfulGeneralBasisState (eigenbasisAsBasis hT0') ({0, 1} : Finset (Fin 3)) ∅).re := by
  have h := dotProduct_star_hubbardOnSiteInteraction_hubbardLowDensityTrialState_re
    hT0' ({0, 1} : Finset (Fin 3)) hmod
  simpa using h

/-- **Red 35 (R6 pinned at a diagonal `t`).** For `t` diagonal (`t := fun i j => if i = j then 3
else 0` on `Fin 2`), the correction term of the number sandwich vanishes term-by-term (the
off-diagonal contribution `Σ_z t_{xz} • ĉ†_{xσ}ĉ_{zσ}` collapses to `t_{xx} • n̂_x`, cancelling the
sandwich's own `t_{xx} • n̂_x` term), so `n̂_x Ĥ^σ n̂_x = n̂_x Ĥ^σ`. A sign slip or a dropped
diagonal term fails this. -/
example :
    fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) *
        hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0) 0 *
        fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0)
      = fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) *
          hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0) 0 := by
  have h := fermionMultiNumber_mul_hubbardKineticSpin_mul_self 1
    (fun i j => if i = j then (3 : ℂ) else 0) 0 (0 : Fin 2)
  simp only [if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)] at h
  simpa using h

/-- **Red 36 (R6 spin-tag guard, mirrors PR-4's Red 19).** The number sandwich at `σ := 0` versus
`σ := 1` on the same diagonal `t` — both hold, and the statement's `spinfulIndex M x σ` must track
`σ`; a hard-coded `σ = 0` inside R6's proof would make the `σ := 1` instance mismatch its own
statement's `spinfulIndex`. -/
example :
    (fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) *
        hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0) 0 *
        fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0)
      = fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) *
          hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0)
          - (∑ z : Fin 2, (if (0 : Fin 2) = z then (3 : ℂ) else 0) •
              (fermionMultiCreation (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) *
                fermionMultiAnnihilation (2 * 1 + 1) (spinfulIndex 1 z 0)))
          + (3 : ℂ) • fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0))
    ∧
    (fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 1) *
        hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0) 1 *
        fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 1)
      = fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 1) *
          hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0)
          - (∑ z : Fin 2, (if (0 : Fin 2) = z then (3 : ℂ) else 0) •
              (fermionMultiCreation (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 1) *
                fermionMultiAnnihilation (2 * 1 + 1) (spinfulIndex 1 z 1)))
          + (3 : ℂ) • fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 1)) := by
  constructor
  · exact fermionMultiNumber_mul_hubbardKineticSpin_mul_self 1
      (fun i j => if i = j then (3 : ℂ) else 0) 0 (0 : Fin 2)
  · exact fermionMultiNumber_mul_hubbardKineticSpin_mul_self 1
      (fun i j => if i = j then (3 : ℂ) else 0) 1 (0 : Fin 2)

/-- **Red 37 (G1 sharpness).** Without the row-sum hypothesis `hK`, the conclusion `‖lam‖ ≤ K` is
*false*: on `Fin 1`, the constant matrix `t := fun _ _ => 2` has `t.mulVec w = (2 : ℂ) • w` for
every `w`, in particular `heig` holds at `lam := 2`, but the row sum `∑ y, ‖t x y‖ = 2` exceeds
`K := 1`, and indeed `‖(2 : ℂ)‖ ≤ 1` is false. Mirrors PR-5 Red 22 / PR-5b Red 30. -/
example :
    ¬ (‖(2 : ℂ)‖ ≤ (1 : ℝ)) ∧
      ((fun _ _ : Fin 1 => (2 : ℂ)).mulVec (fun _ : Fin 1 => (1 : ℂ))
        = (2 : ℂ) • (fun _ : Fin 1 => (1 : ℂ))) ∧
      ¬ (∀ x : Fin 1, ∑ y : Fin 1, ‖(fun _ _ : Fin 1 => (2 : ℂ)) x y‖ ≤ (1 : ℝ)) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · funext x; simp [Matrix.mulVec, Matrix.dotProduct]
  · intro h
    have := h 0
    simp at this

/-- **Red 38 (V6 non-vacuity).** The Roth projection does not annihilate the trial state on the
`Red 32` fixture: `0 < ‖Ψ̃‖²`, guarding against a "bound proved because both sides are 0"
degeneracy hiding inside Red 32. -/
example :
    0 < (star (hubbardLowDensityRothState (eigenbasisAsBasis hT0) (∅ : Finset (Fin 2))
          (v := ![1 / Real.sqrt 2, 1 / Real.sqrt 2])) ⬝ᵥ
        hubbardLowDensityRothState (eigenbasisAsBasis hT0) (∅ : Finset (Fin 2))
          (v := ![1 / Real.sqrt 2, 1 / Real.sqrt 2])).re := by
  have hmod : ∀ x : Fin 2, ‖(![1 / Real.sqrt 2, 1 / Real.sqrt 2] : Fin 2 → ℂ) x‖ ^ 2
      = 1 / ((1 : ℝ) + 1) := by
    intro x
    fin_cases x <;>
      simp [Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_nonneg, Real.sq_sqrt,
        Real.sqrt_nonneg]
  have hhalf : 2 * ((∅ : Finset (Fin 2)).card : ℝ) ≤ (1 : ℝ) + 1 := by simp
  exact dotProduct_star_self_hubbardLowDensityRothState_pos hT0 (∅ : Finset (Fin 2)) hmod hhalf

/-- **Red 39 (`hhalf` sharpness).** Without `2 * SUp.card ≤ M + 1`, the constant `8` is not
enough: the standalone real inequality `E * (1 - ρ) + 4 * K * ρ ≤ (E + 8 * K * ρ) * (1 - ρ)`, which
underlies step (h) of the assembly, fails at `ρ → 1` (`E := 0`, `K := 1`): the left side tends to
`4` while the right side tends to `0`. Documents why `hhalf` (`ρ ≤ 1/2`) is load-bearing rather
than convenient. -/
example :
    ¬ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      (0 : ℝ) * (1 - ρ) + 4 * 1 * ρ ≤ ((0 : ℝ) + 8 * 1 * ρ) * (1 - ρ) := by
  intro h
  have := h 1 (by norm_num) (le_refl 1)
  norm_num at this

end LatticeSystem.Tests.HubbardImpossibilityLowDensityRoth
