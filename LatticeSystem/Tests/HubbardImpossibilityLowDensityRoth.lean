import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensity
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityTrial
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityRothCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityRoth
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityFloor
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandEigenbasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUTrial
import LatticeSystem.Fermion.JordanWigner.Hubbard.ChargesCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.AllUpState
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJAllUpProperties
import LatticeSystem.Math.MatrixAnalysis.RowSumEigenvalueBound
import LatticeSystem.Math.MonotoneEnumeration
import LatticeSystem.Math.Analysis.RpowSublinearThreshold
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Test coverage for Theorem 11.4 PR-6 (Roth's variational bound)

Continues the numbering of `LatticeSystem.Tests.HubbardImpossibilityLowDensity` (which ends at
Red 31) in a sibling module, per the PR-6 design (`.self-local/docs/theorem-11-4-pr6-design.md`
§5/§8 decision 3): the existing module is already at 714 lines, past the 700-line review trigger.

These tests pin the three PR-6 modules:

* `LatticeSystem.Math.MatrixAnalysis.RowSumEigenvalueBound` — the generic Gershgorin row-sum
  corollary `norm_le_of_mulVec_eq_smul_of_rowSum_le` (G1).
* `LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityRothCore` — the
  number-sandwich identity `fermionMultiNumber_mul_hubbardKineticSpin_mul_self` (R6) and its
  supporting lemmas.
* `LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityRoth` — the Roth state
  `hubbardLowDensityRothState` and the capstone Rayleigh bound
  `rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le`, with the intermediate
  double-occupancy weight
  `dotProduct_star_hubbardOnSiteInteraction_hubbardLowDensityTrialState` and positivity
  `dotProduct_star_self_hubbardLowDensityRothState_pos`.

- **Red 32 (primary consumption, Method D)**: the capstone at `M := 1`, `SUp := ∅`, `t := 0`,
  the uniform ↓ orbital `v := 1/√2` (so `hmod` holds with `e₁ := 0`, `K := 0`, `hhalf` holds
  vacuously): the bound collapses to `rayleighOnVec Ĥ Ψ̃ ≤ 0`. Every binder is exercised at once.
- **Red 33 (`U`-independence, the theorem's headline)**: the capstone instantiated at two distinct
  `U` values on the same fixture produces the *same* numeral bound — Theorem 11.4 holds for every
  `U`, and a proof that accidentally retained a `U`-dependent term would fail this test.
- **Red 34 / 34b (the `1/Ns` factor)**: the double-occupancy weight at `M := 1`, `SUp := {0}`
  (ratio `1/2`) and `M := 2`, `SUp := {0, 1}` (ratio `2/3`), pinning `SUp.card / (M + 1)` as a
  genuine ratio rather than a coincidence at one fixture (the PR-5 Red 20/21 discipline).
- **Red 35 (the sandwich at a diagonal `t`)**: for `t` diagonal the correction term of the number
  sandwich cancels the diagonal term, so `n̂ Ĥ^σ n̂ = n̂ Ĥ^σ`. Guards a sign slip or a dropped
  diagonal term.
- **Red 36 (spin-tag guard)**: the sandwich at `σ := 0` versus `σ := 1` on the same `t` — both
  hold, and the statement's `spinfulIndex M x σ` must track `σ` (mirrors PR-4's Red 19).
- **Red 37 (G1 sharpness)**: without the row-sum hypothesis `hK`, the conclusion `‖lam‖ ≤ K` is
  false: on `Fin 1`, `t := fun _ _ => 2`, `lam := 2`, `K := 1` — the row sum is `2 > 1`. Standalone,
  mirrors PR-5 Red 22 / PR-5b Red 30.
- **Red 38 (non-vacuity)**: `0 < ‖Ψ̃‖²` at a concrete configuration — the Roth projection does not
  annihilate the trial state, guarding against a "bound proved because both sides are 0"
  degeneracy in Red 32.
- **Red 39 (`hhalf` sharpness)**: without `2 * SUp.card ≤ M + 1` the constant `8` is not enough;
  exhibited as a standalone real-inequality failure at `ρ := SUp.card / (M + 1) → 1`.
- **Red 40 (capstone consumption at a nonempty `SUp`)**: Red 32's fixture with `SUp := {0}`, where
  `ρ = 1/2`, `hhalf` is saturated rather than vacuous and `Ψ̃ ≠ Ψ` — the corrections act on a
  nonzero doubly occupied component. Red 32/33/38 all run at `SUp := ∅`, where the Roth
  construction degenerates.
- **Red 41 (the Roth norm ratio at a nonempty `SUp`)**: `‖Ψ̃‖² = (1 − ρ)‖Φ↑‖²` read off at
  `SUp := {0}`, pinning the factor `1 − ρ` that is invisible at `SUp := ∅`.

The site parameter `M` is a numeral at every fixture, so the modulus hypothesis is written with
the natural-number coercion `((1 : ℕ) : ℝ)` that the statement's `(M : ℝ)` elaborates to.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.4, eqs. (11.1.9)/(11.1.10), p. 376; Tasaki, Prog. Theor. Phys. **99**
(1998) 489, Theorem 3.3, Appendix F, eqs. (F.1)–(F.3) and (F.8)–(F.13), pp. 545–546.
-/

namespace LatticeSystem.Tests.HubbardImpossibilityLowDensityRoth

open LatticeSystem.Fermion
open LatticeSystem.Math
open LatticeSystem.Quantum

open scoped BigOperators ComplexOrder

/-- Fixture: the zero hopping matrix on `Fin 2` is Hermitian, its eigenvalues are all `0`. -/
private noncomputable def hT0 : (0 : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
  unfold Matrix.IsHermitian
  simp

/-- Fixture: the uniform ↓ orbital on two sites, `v_x = 1/√2`. -/
private noncomputable def vUniform : Fin 2 → ℂ := fun _ => ((1 / Real.sqrt 2 : ℝ) : ℂ)

/-- Fixture: the uniform ↓ orbital has squared modulus `1/2` at every site. -/
private theorem vUniform_mod (x : Fin 2) : ‖vUniform x‖ ^ 2 = 1 / (((1 : ℕ) : ℝ) + 1) := by
  rw [vUniform, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, one_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Fixture: the uniform ↓ orbital is a zero eigenvector of the zero hopping matrix. -/
private theorem vUniform_eig :
    (0 : Matrix (Fin 2) (Fin 2) ℂ).mulVec vUniform = ((0 : ℝ) : ℂ) • vUniform := by
  rw [Matrix.zero_mulVec, Complex.ofReal_zero, zero_smul]

/-- Fixture: the zero hopping matrix has vanishing row sums. -/
private theorem zero_rowSum (x : Fin 2) :
    ∑ y : Fin 2, ‖(0 : Matrix (Fin 2) (Fin 2) ℂ) x y‖ ≤ (0 : ℝ) := by
  simp

/-- Fixture: the empty occupied set satisfies the half-filling side condition vacuously. -/
private theorem empty_half : 2 * ((∅ : Finset (Fin 2)).card : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 := by
  norm_num

/-- Fixture: the Slater energy of the empty occupied set vanishes. -/
private theorem occ_empty_re : (occupiedEigenEnergy hT0 (∅ : Finset (Fin 2)) ∅).re = 0 := by
  rw [occupiedEigenEnergy, Finset.sum_empty, add_zero, Complex.zero_re]

/-- **Red 32 (primary consumption, Method D).** At `M := 1`, `SUp := ∅`, `t := 0`, the uniform ↓
orbital `v_x = 1/√2` (`hmod` holds since `‖v x‖ ^ 2 = 1/2`), `e₁ := 0` (`t.mulVec v = 0 = 0 • v`),
`K := 0` (the zero matrix's row sums are `0`), `hhalf` vacuous (`SUp.card = 0`): the capstone bound
collapses to `rayleighOnVec Ĥ Ψ̃ ≤ 0`. This is the single hardest consumption test — every binder of
the capstone is exercised at once. -/
example (U : ℝ) :
    rayleighOnVec (hubbardHamiltonian 1 (0 : Matrix (Fin 2) (Fin 2) ℂ) (U : ℂ))
        (hubbardLowDensityRothState (eigenbasisAsBasis hT0) (∅ : Finset (Fin 2)) vUniform)
      ≤ 0 := by
  have hbound := rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le
    hT0 (∅ : Finset (Fin 2)) vUniform_eig vUniform_mod zero_rowSum empty_half U
  rw [occ_empty_re] at hbound
  simpa using hbound

/-- **Red 33 (`U`-independence, the theorem's headline).** The capstone at two distinct `U` values
on the `Red 32` fixture produces the *literally same* numeral bound `0` — Theorem 11.4 holds for
every `U ≥ 0`, and a proof that accidentally kept a `U`-dependent term would fail this test. -/
example :
    (rayleighOnVec (hubbardHamiltonian 1 (0 : Matrix (Fin 2) (Fin 2) ℂ) ((0 : ℝ) : ℂ))
        (hubbardLowDensityRothState (eigenbasisAsBasis hT0) (∅ : Finset (Fin 2)) vUniform) ≤ 0)
    ∧
    (rayleighOnVec (hubbardHamiltonian 1 (0 : Matrix (Fin 2) (Fin 2) ℂ) ((5 : ℝ) : ℂ))
        (hubbardLowDensityRothState (eigenbasisAsBasis hT0) (∅ : Finset (Fin 2)) vUniform)
      ≤ 0) := by
  constructor
  · have hbound := rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le
      hT0 (∅ : Finset (Fin 2)) vUniform_eig vUniform_mod zero_rowSum empty_half (0 : ℝ)
    rw [occ_empty_re] at hbound
    simpa using hbound
  · have hbound := rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le
      hT0 (∅ : Finset (Fin 2)) vUniform_eig vUniform_mod zero_rowSum empty_half (5 : ℝ)
    rw [occ_empty_re] at hbound
    simpa using hbound

/-- Fixture: the zero hopping matrix on `Fin 3` (`M := 2`) is Hermitian. -/
private noncomputable def hT0' : (0 : Matrix (Fin 3) (Fin 3) ℂ).IsHermitian := by
  unfold Matrix.IsHermitian
  simp

/-- **Red 34 (the `1/Ns` factor at `M := 1`).** With `SUp := {0}` (`SUp.card = 1`, `M + 1 = 2`) the
double-occupancy weight is `D = (1/2) · ‖Φ↑‖²`. A lost `1/Ns` factor or an `Ne` vs. `Ne − 1` slip
breaks exactly this ratio. -/
example {v : Fin 2 → ℂ} (hmod : ∀ x, ‖v x‖ ^ 2 = 1 / (((1 : ℕ) : ℝ) + 1)) :
    (star (hubbardLowDensityTrialState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) v) ⬝ᵥ
        (hubbardOnSiteInteraction 1 1).mulVec
          (hubbardLowDensityTrialState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) v)).re
      = (1 / 2 : ℝ) *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) ∅) ⬝ᵥ
            spinfulGeneralBasisState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) ∅).re := by
  rw [dotProduct_star_hubbardOnSiteInteraction_hubbardLowDensityTrialState hT0
      ({0} : Finset (Fin 2)) hmod, Complex.re_ofReal_mul]
  norm_num

/-- **Red 34b (the `1/Ns` factor at `M := 2`).** With `SUp := {0, 1}` (`SUp.card = 2`, `M + 1 = 3`)
the ratio is `2/3`, run at a second fixture so `SUp.card / (M + 1)` is pinned as a genuine shape
rather than a coincidence at Red 34's `1/2`. -/
example {v : Fin 3 → ℂ} (hmod : ∀ x, ‖v x‖ ^ 2 = 1 / (((2 : ℕ) : ℝ) + 1)) :
    (star (hubbardLowDensityTrialState (eigenbasisAsBasis hT0') ({0, 1} : Finset (Fin 3)) v) ⬝ᵥ
        (hubbardOnSiteInteraction 2 1).mulVec
          (hubbardLowDensityTrialState (eigenbasisAsBasis hT0') ({0, 1} : Finset (Fin 3)) v)).re
      = (2 / 3 : ℝ) *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT0') ({0, 1} : Finset (Fin 3)) ∅) ⬝ᵥ
            spinfulGeneralBasisState (eigenbasisAsBasis hT0') ({0, 1} : Finset (Fin 3)) ∅).re := by
  rw [dotProduct_star_hubbardOnSiteInteraction_hubbardLowDensityTrialState hT0'
      ({0, 1} : Finset (Fin 3)) hmod, Complex.re_ofReal_mul]
  norm_num

/-- **Red 35 (the sandwich at a diagonal `t`).** For `t` diagonal (`t := fun i j => if i = j then 3
else 0` on `Fin 2`), the correction sum `Σ_z t_{0z} • ĉ†_0ĉ_z` collapses to `3 • n̂_0`, which
cancels the sandwich's own `t_{00} • n̂_0` term, so `n̂_0 Ĥ^σ n̂_0 = n̂_0 Ĥ^σ`. A sign slip or a
dropped diagonal term fails this. -/
example :
    fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) *
        hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0) 0 *
        fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0)
      = fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) *
          hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0) 0 := by
  have h := fermionMultiNumber_mul_hubbardKineticSpin_mul_self 1
    (fun i j => if i = j then (3 : ℂ) else 0) 0 (0 : Fin 2)
  have hcorr : (∑ z : Fin 2, (if (0 : Fin 2) = z then (3 : ℂ) else 0) •
        (fermionMultiCreation (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) *
          fermionMultiAnnihilation (2 * 1 + 1) (spinfulIndex 1 z 0)))
      = (3 : ℂ) • fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) := by
    rw [Finset.sum_eq_single (0 : Fin 2)]
    · rw [if_pos rfl]
      rfl
    · intro z _ hz
      rw [if_neg (Ne.symm hz), zero_smul]
    · intro hz
      exact absurd (Finset.mem_univ (0 : Fin 2)) hz
  rw [hcorr, if_pos rfl] at h
  rw [h]
  abel

/-- **Red 36 (spin-tag guard, mirrors PR-4's Red 19).** The number sandwich at `σ := 0` versus
`σ := 1` on the same diagonal `t` — both hold, and the statement's `spinfulIndex M x σ` must track
`σ`; a hard-coded `σ = 0` inside the proof would make the `σ := 1` instance mismatch its own
statement's `spinfulIndex`. -/
example :
    (fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) *
        hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0) 0 *
        fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0)
      = fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) *
          hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0) 0
          - (∑ z : Fin 2, (if (0 : Fin 2) = z then (3 : ℂ) else 0) •
              (fermionMultiCreation (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0) *
                fermionMultiAnnihilation (2 * 1 + 1) (spinfulIndex 1 z 0)))
          + (3 : ℂ) • fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 0))
    ∧
    (fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 1) *
        hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0) 1 *
        fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 1)
      = fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 1) *
          hubbardKineticSpin 1 (fun i j => if i = j then (3 : ℂ) else 0) 1
          - (∑ z : Fin 2, (if (0 : Fin 2) = z then (3 : ℂ) else 0) •
              (fermionMultiCreation (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 1) *
                fermionMultiAnnihilation (2 * 1 + 1) (spinfulIndex 1 z 1)))
          + (3 : ℂ) • fermionMultiNumber (2 * 1 + 1) (spinfulIndex 1 (0 : Fin 2) 1)) := by
  refine ⟨?_, ?_⟩
  · have h := fermionMultiNumber_mul_hubbardKineticSpin_mul_self 1
      (fun i j => if i = j then (3 : ℂ) else 0) 0 (0 : Fin 2)
    rwa [if_pos rfl] at h
  · have h := fermionMultiNumber_mul_hubbardKineticSpin_mul_self 1
      (fun i j => if i = j then (3 : ℂ) else 0) 1 (0 : Fin 2)
    rwa [if_pos rfl] at h

/-- **Red 37 (G1 sharpness).** Without the row-sum hypothesis `hK`, the conclusion `‖lam‖ ≤ K` is
*false*: on `Fin 1`, the constant matrix `t := fun _ _ => 2` has `t.mulVec w = (2 : ℂ) • w` for
every constant `w`, in particular the eigen-equation holds at `lam := 2`, but the row sum
`∑ y, ‖t x y‖ = 2` exceeds `K := 1`, and indeed `‖(2 : ℂ)‖ ≤ 1` is false. Mirrors PR-5 Red 22 /
PR-5b Red 30. -/
example :
    ¬ (‖(2 : ℂ)‖ ≤ (1 : ℝ)) ∧
      (Matrix.mulVec (fun _ _ : Fin 1 => (2 : ℂ)) (fun _ : Fin 1 => (1 : ℂ))
        = (2 : ℂ) • (fun _ : Fin 1 => (1 : ℂ))) ∧
      ¬ (∀ x : Fin 1, ∑ y : Fin 1, ‖(fun _ _ : Fin 1 => (2 : ℂ)) x y‖ ≤ (1 : ℝ)) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · funext x
    simp [Matrix.mulVec, dotProduct]
  · intro h
    have h0 := h 0
    simp at h0

/-- **Red 38 (non-vacuity).** The Roth projection does not annihilate the trial state on the
`Red 32` fixture: `0 < ‖Ψ̃‖²`, guarding against a "bound proved because both sides are 0"
degeneracy hiding inside Red 32. -/
example :
    0 < (star (hubbardLowDensityRothState (eigenbasisAsBasis hT0) (∅ : Finset (Fin 2))
          vUniform) ⬝ᵥ
        hubbardLowDensityRothState (eigenbasisAsBasis hT0) (∅ : Finset (Fin 2)) vUniform).re :=
  dotProduct_star_self_hubbardLowDensityRothState_pos hT0 (∅ : Finset (Fin 2)) vUniform_mod
    empty_half

/-- **Red 39 (`hhalf` sharpness).** Without `2 * SUp.card ≤ M + 1`, the constant `8` is not
enough: the standalone real inequality `E * (1 - ρ) + 4 * K * ρ ≤ (E + 8 * K * ρ) * (1 - ρ)`, which
underlies the assembly of the capstone, fails at `ρ → 1` (`E := 0`, `K := 1`): the left side tends
to `4` while the right side tends to `0`. Documents why `hhalf` (`ρ ≤ 1/2`) is load-bearing rather
than convenient. -/
example :
    ¬ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
      (0 : ℝ) * (1 - ρ) + 4 * 1 * ρ ≤ ((0 : ℝ) + 8 * 1 * ρ) * (1 - ρ) := by
  intro h
  have h1 := h 1 (by norm_num) (le_refl 1)
  norm_num at h1

/-- Fixture: the singleton occupied set saturates the half-filling side condition, `2 · 1 ≤ 1 + 1`,
so the density is `ρ = 1/2` rather than `0`. -/
private theorem singleton_half :
    2 * ((({0} : Finset (Fin 2)).card : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 := by
  norm_num

/-- Fixture: the Slater energy of the singleton occupied set vanishes, since the zero hopping
matrix has vanishing row sums and hence vanishing eigenvalues. -/
private theorem occ_singleton_re :
    (occupiedEigenEnergy hT0 ({0} : Finset (Fin 2)) ∅).re = 0 := by
  have h0 : hT0.eigenvalues 0 = 0 :=
    abs_nonpos_iff.mp (abs_eigenvalues_le_of_rowSum_le hT0 zero_rowSum 0)
  rw [occupiedEigenEnergy, Finset.sum_empty, add_zero, Finset.sum_singleton, h0,
    Complex.ofReal_zero, Complex.zero_re]

/-- **Red 40 (capstone consumption at a nonempty `SUp`).** The same `M := 1`, `t := 0`, `K := 0`,
`e₁ := 0` fixture as Red 32, but with `SUp := {0}`: now `ρ = |SUp|/(M+1) = 1/2`, `hhalf` is
saturated rather than vacuous, `ν̂Ψ ≠ 0`, and `Ψ̃ = Ψ − ν̂Ψ` is a genuine projection rather than `Ψ`
itself.  Both corrections `V4`/`V5` are therefore applied to a nonzero doubly occupied component,
and the residual `8K|SUp|/(M+1)` is forced to vanish exactly, so the bound is the tightest one the
fixture admits: `rayleighOnVec Ĥ Ψ̃ ≤ 0`.  Red 32/33/38 all run at `SUp := ∅`, where the whole Roth
construction degenerates; this instance shows the capstone's hypotheses are jointly satisfiable in
the regime it was built for. -/
example (U : ℝ) :
    rayleighOnVec (hubbardHamiltonian 1 (0 : Matrix (Fin 2) (Fin 2) ℂ) (U : ℂ))
        (hubbardLowDensityRothState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) vUniform)
      ≤ 0 := by
  have hbound := rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le
    hT0 ({0} : Finset (Fin 2)) vUniform_eig vUniform_mod zero_rowSum singleton_half U
  rw [occ_singleton_re] at hbound
  simpa using hbound

/-- **Red 41 (the Roth norm ratio `1 − ρ` at a nonempty `SUp`).** At `SUp := {0}` the projection
removes exactly half of the trial norm: `‖Ψ̃‖² = (1/2)‖Φ↑‖²`.  A dropped or inverted `1 − ρ` factor,
invisible at `SUp := ∅` (where `Ψ̃ = Ψ`), fails here. -/
example :
    (star (hubbardLowDensityRothState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) vUniform) ⬝ᵥ
        hubbardLowDensityRothState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) vUniform).re
      = (1 / 2 : ℝ) *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) ∅) ⬝ᵥ
          spinfulGeneralBasisState (eigenbasisAsBasis hT0) ({0} : Finset (Fin 2)) ∅).re := by
  rw [dotProduct_star_self_hubbardLowDensityRothState_re hT0 ({0} : Finset (Fin 2)) vUniform_mod]
  norm_num

/-!
## Theorem 11.4 PR-7b — the fractional-knapsack lemmas and the ferromagnetic floor

Continues the numbering from PR-7a (Red 44), starting at Red 48.  Reds 45–47 and Red 51 were
reserved for PR-7c; they are filled in below (§ PR-7c), together with Reds 54/54b.  These Reds pin
the PR-7b consumption of:

* `LatticeSystem.Math.sum_lowestLevels_le_sum_weighted` (W1, the fractional-knapsack lemma) and
  `LatticeSystem.Math.sum_lowestLevels_le_sum_weighted_of_map_eq` (W2, its reading against the
  unsorted spectrum; `Tests.HubbardImpossibilityLowDensity`'s Red 27 pins W2 on the
  `{0, 1}`-valued fixture, so the fixtures here are the genuinely fractional ones);
* `one_sub_eigenNumberOp_posSemidef` (F1),
  `hubbardOnSiteInteraction_mulVec_eq_zero_of_downNumber_zero` (F2) and
  `fermionTotalDownNumber_mulVec_eq_zero_of_topWeight` (F3), the three algebraic ingredients of the
  ferromagnetic floor.

Each Red is a *consumption* test: it instantiates the named declaration and asserts the numeric or
operator-level consequence, so a statement-only or direction-flipped version fails to compile.
-/

/-- **Red 48 (W1 pinned, the fractional regime).** `m = 3`, `ε := fun i => (i : ℝ)` (so
`ε = ![0, 1, 2]` at the three fixture indices), `k = 2`, `w := ![1, 1/2, 1/2]`: `∑ w = 2` and the
half-integral weights give `∑ i : Fin 2, ε (castLE i) = 0 + 1 = 1 ≤ 0·1 + 1·(1/2) + 2·(1/2) = 3/2`.
The half-integral (not `{0, 1}`-valued) weight is the point: a proof that only handles the
deleted `sum_lowestLevels_le_sum_of_monotone`'s `{0, 1}`-valued indicator weights fails to
instantiate here. -/
example : (1 : ℝ) ≤ 3 / 2 := by
  have hmono : Monotone (fun i : Fin 3 => (i : ℝ)) := fun a b hab => by
    change (a : ℝ) ≤ (b : ℝ)
    have h : (a : ℕ) ≤ (b : ℕ) := hab
    exact_mod_cast h
  set w : Fin 3 → ℝ := ![1, 1 / 2, 1 / 2] with hw_def
  have hw0 : ∀ j, 0 ≤ w j := fun j => by fin_cases j <;> norm_num [hw_def]
  have hw1 : ∀ j, w j ≤ 1 := fun j => by fin_cases j <;> norm_num [hw_def]
  have hsum : ∑ j, w j = (2 : ℕ) := by
    change (∑ j, w j : ℝ) = 2
    simp [hw_def, Fin.sum_univ_three]
    norm_num
  have hk : (2 : ℕ) ≤ 3 := by decide
  have h := LatticeSystem.Math.sum_lowestLevels_le_sum_weighted hk hmono hw0 hw1 hsum
  have hlhs : (∑ i : Fin 2, (fun i : Fin 3 => (i : ℝ)) (Fin.castLE hk i)) = 1 := by
    simp [Fin.sum_univ_two]
  have hrhs : (∑ j : Fin 3, (fun i : Fin 3 => (i : ℝ)) j * w j) = 3 / 2 := by
    simp [hw_def, Fin.sum_univ_three]
    norm_num
  rw [hlhs, hrhs] at h
  exact h

/-- **Red 49 (W1 sharpness: `w ≤ 1` is load-bearing).** Standalone, references neither W1 nor W2.
With `ε := fun i => (i : ℝ)`, `k = 2`, `w := ![2, 0, 0]`: `∑ w = 2` and `0 ≤ w`, but
`∑ j, ε j * w j = 0 < 1 = ∑ i : Fin 2, ε (castLE i)`. Documents why `hw1` cannot be dropped from
W1's hypotheses. -/
example :
    ¬ (∑ i : Fin 2, (fun i : Fin 3 => (i : ℝ)) (Fin.castLE (by decide : (2 : ℕ) ≤ 3) i)
        ≤ ∑ j : Fin 3, (fun i : Fin 3 => (i : ℝ)) j * (![2, 0, 0] : Fin 3 → ℝ) j) := by
  have hlhs : (∑ i : Fin 2, (fun i : Fin 3 => (i : ℝ))
      (Fin.castLE (by decide : (2 : ℕ) ≤ 3) i)) = 1 := by
    simp [Fin.sum_univ_two]
  have hrhs : (∑ j : Fin 3, (fun i : Fin 3 => (i : ℝ)) j * (![2, 0, 0] : Fin 3 → ℝ) j) = 0 := by
    simp [Fin.sum_univ_three]
  rw [hlhs, hrhs]
  norm_num

/-- **Red 50 (W2 pinned on an unsorted `g`).** `ε := fun i => (i : ℝ)`, `g := ![1, 2, 0] : Fin 3 →
ℝ` (a genuine cyclic rotation of `ε`'s values, so `hspec` is proved via `List.rotate_perm` rather
than PR-5b's `decide`, which does not reduce on `ℝ`), `k = 2`, `w := ![1, 1/2, 1/2]`: `∑ w = 2` and
`∑ j, g j * w j = 1·1 + 2·(1/2) + 0·(1/2) = 2 ≥ 1 = ∑ i : Fin 2, ε (castLE i)`. Guards the
sorting-transport step of W2 at a genuinely unsorted `g` and a fractional weight. -/
example : (1 : ℝ) ≤ 2 := by
  have hmono : Monotone (fun i : Fin 3 => (i : ℝ)) := fun a b hab => by
    change (a : ℝ) ≤ (b : ℝ)
    have h : (a : ℕ) ≤ (b : ℕ) := hab
    exact_mod_cast h
  have hspec : (Finset.univ : Finset (Fin 3)).val.map (fun i : Fin 3 => (i : ℝ))
      = (Finset.univ : Finset (Fin 3)).val.map (![1, 2, 0] : Fin 3 → ℝ) := by
    rw [Fin.univ_val_map, Fin.univ_val_map]
    have hofFnε : List.ofFn (fun i : Fin 3 => (i : ℝ)) = [0, 1, 2] := by
      simp [List.ofFn_succ, List.ofFn_zero]
      norm_num
    have hofFng : List.ofFn (![1, 2, 0] : Fin 3 → ℝ) = [1, 2, 0] := by
      simp [List.ofFn_succ, List.ofFn_zero]
    rw [hofFnε, hofFng]
    have hrot : ([0, 1, 2] : List ℝ).rotate 1 = [1, 2, 0] := by rfl
    exact Multiset.coe_eq_coe.mpr (hrot ▸ (List.rotate_perm ([0, 1, 2] : List ℝ) 1).symm)
  set w : Fin 3 → ℝ := ![1, 1 / 2, 1 / 2] with hw_def
  have hw0 : ∀ j, 0 ≤ w j := fun j => by fin_cases j <;> norm_num [hw_def]
  have hw1 : ∀ j, w j ≤ 1 := fun j => by fin_cases j <;> norm_num [hw_def]
  have hsum : ∑ j, w j = (2 : ℕ) := by
    change (∑ j, w j : ℝ) = 2
    simp [hw_def, Fin.sum_univ_three]
    norm_num
  have hk : (2 : ℕ) ≤ 3 := by decide
  have h := LatticeSystem.Math.sum_lowestLevels_le_sum_weighted_of_map_eq hk hmono hspec hw0 hw1
    hsum
  have hlhs : (∑ i : Fin 2, (fun i : Fin 3 => (i : ℝ)) (Fin.castLE hk i)) = 1 := by
    simp [Fin.sum_univ_two]
  have hrhs : (∑ j : Fin 3, (![1, 2, 0] : Fin 3 → ℝ) j * w j) = 2 := by
    simp [hw_def, Fin.sum_univ_three]
    norm_num
  rw [hlhs, hrhs] at h
  exact h

/-- **Red 52 (F1 pinned).** `1 − n̂_{j,σ}` is positive-semidefinite for the eigenmode number
operator on the `Red 32` fixture (`M := 1`, `hT0` the zero hopping matrix on `Fin 2`), at `j := 0`,
`σ := 0`. What is guarded is the orientation of F1's *statement*: it is `1 − n̂_{j,σ}`, not
`n̂_{j,σ} − 1`, that is asserted positive-semidefinite, which is the direction the occupation weight
`w_j ≤ 1` is read off from. The `A·Aᴴ` versus `Aᴴ·A` step inside F1's proof needs no guarding: the
goal fixes `n̂_{j,σ} = Aᴴ·A`, so a flip there fails to typecheck. -/
example :
    ((1 : ManyBodyOp (Fin 4)) - eigenNumberOp hT0 (0 : Fin 2) (0 : Fin 2)).PosSemidef :=
  one_sub_eigenNumberOp_posSemidef hT0 (0 : Fin 2) (0 : Fin 2)

/-- **Red 52b (F2 pinned).** The on-site interaction annihilates the Fock vacuum at `M := 1`,
`U := 5`, via the vacuum's own `N̂_↓ = 0` fact (`fermionTotalDownNumber_mulVec_vacuum`). A minimal
non-trivial consumption of F2's hypothesis-to-conclusion shape. -/
example : (hubbardOnSiteInteraction 1 (5 : ℂ)).mulVec (fermionMultiVacuum 3) = 0 :=
  hubbardOnSiteInteraction_mulVec_eq_zero_of_downNumber_zero 1 (5 : ℂ)
    (fermionTotalDownNumber_mulVec_vacuum 1)

/-- Fixture: the all-up Slater state on `N := 1` (`Ne = N + 1 = 2` electrons) is annihilated by
`N̂_↓`, built from `AllUpState.lean`'s per-site fact
(`fermionDownNumber_mulVec_allUpState`) summed over the two sites. -/
private theorem allUpState_one_down_zero :
    (fermionTotalDownNumber 1).mulVec (hubbardAllUpState 1) = 0 := by
  unfold fermionTotalDownNumber
  rw [Matrix.sum_mulVec]
  exact Finset.sum_eq_zero fun i _ => fermionDownNumber_mulVec_allUpState 1 i

/-- Fixture: the all-up Slater state on `N := 1` has `N̂_↑ = 2`, built from
`fermionUpNumber_mulVec_allUpState` summed over the two sites. -/
private theorem allUpState_one_up_two :
    (fermionTotalUpNumber 1).mulVec (hubbardAllUpState 1)
      = ((2 : ℕ) : ℂ) • hubbardAllUpState 1 := by
  unfold fermionTotalUpNumber
  rw [Matrix.sum_mulVec]
  simp [fermionUpNumber_mulVec_allUpState, two_smul]

/-- Fixture: the all-up Slater state on `N := 1` is a `N̂_tot = 2` eigenvector, from
`allUpState_one_up_two`, `allUpState_one_down_zero` and `fermionTotalNumber_eq_up_add_down`. -/
private theorem allUpState_one_number_two :
    (fermionTotalNumber (2 * 1 + 1)).mulVec (hubbardAllUpState 1)
      = ((2 : ℕ) : ℂ) • hubbardAllUpState 1 := by
  rw [fermionTotalNumber_eq_up_add_down, Matrix.add_mulVec, allUpState_one_up_two,
    allUpState_one_down_zero, add_zero]

/-- Fixture: the all-up Slater state on `N := 1` is a `Ŝᶻ_tot = 1` eigenvector — `(2/2 : ℝ)` cast to
`ℂ`, matching F3's `hZ` shape — from `fermionTotalSpinZ`'s definition, `allUpState_one_up_two` and
`allUpState_one_down_zero`. -/
private theorem allUpState_one_spinZ :
    (fermionTotalSpinZ 1).mulVec (hubbardAllUpState 1)
      = ((((2 : ℕ) : ℝ) / 2 : ℝ) : ℂ) • hubbardAllUpState 1 := by
  rw [fermionTotalSpinZ, Matrix.smul_mulVec, Matrix.sub_mulVec, allUpState_one_up_two,
    allUpState_one_down_zero, sub_zero, smul_smul]
  congr 1
  push_cast
  ring

/-- **Red 53 (F3 pinned).** The all-up Slater state on `N := 1` (`Ne := 2`, the top-weight state
of a fully polarised two-electron sector) really has `N̂_↓ = 0` via F3. A dropped factor `2` in the
`Ŝᶻ_tot` definition, or an off-by-one in `Ne`, fails to unify `allUpState_one_spinZ`'s conclusion
with F3's `hZ` hypothesis. -/
example : (fermionTotalDownNumber 1).mulVec (hubbardAllUpState 1) = 0 :=
  fermionTotalDownNumber_mulVec_eq_zero_of_topWeight allUpState_one_number_two allUpState_one_spinZ

/-!
## Theorem 11.4 PR-7c — the `rpow` threshold (T1) and the ferromagnetic-floor capstone (F4)

Fills the reserved Reds 45–47 and 51 (the PR-7b placeholder above), adds Reds 54/54b for F4 and
Red 55 for the discharged capstone. The two names pinned here are
`T1 = LatticeSystem.Math.exists_pos_forall_mul_lt_rpow` (the `rpow` threshold) and
`F4 = LatticeSystem.Fermion.sum_lowestLevels_mul_le_rayleighOnVec_hubbardKinetic` (the
ferromagnetic floor), the two ingredients out of which `hubbard_theorem_11_4` is assembled.

* **Red 45 / 46 / 47 (T1 consumption at three fixture triples).** Three independent instantiations
  of T1 at different `(a, b, p)`, each obtaining the witness `r` and applying it at a concrete
  density inside `(0, r]`. Red 46 additionally applies the *same* obtained `r` at two different
  densities (`r/2` and `r/4`) — this is the load-bearing content: `r` is chosen once, before any
  density is picked, exactly as `ρ₁` in `hubbard_theorem_11_4` is chosen before `N`.
  **Note the point being guarded**: Red 46 is not exercising a nontrivial band condition (there is
  none here — T1 has no such hypothesis); the fact it pins is purely that *one* witness `r` serves
  *both* densities simultaneously, mirroring the PR-6 Red 38 lesson that a "both sides vacuous"
  instance must not be mistaken for genuine content. Red 47 instead varies `(a, b)` while holding
  `p` fixed, obtaining two independent witnesses, guarding that T1's conclusion is not accidentally
  tied to one specific numeral pair.
* **Red 51 (T1 pinned + `p < 1` sharpness).** The primary pinned instance at `a = b = 1`,
  `p = 1/2`, plus a **standalone** counterexample at `p = 1` referencing neither T1 nor any fixture:
  `1 * 1 < 1 * 1 ^ (1 : ℝ)` is false, so `hp1 : p < 1` cannot be dropped from T1's hypotheses.
* **Red 54 (F4 at `t = 0`, the degenerate floor).** `M := 1`, `t := 0` (fixture `hT0`), `ε := 0`
  (`hspec` via `hT0.eigenvalues = 0`), the `Ne := 2` all-up Slater state `hubbardAllUpState 1`
  (`hdown`/`hnum` from the `Red 53` machinery, `hu0` from `hubbardAllUpState_ne_zero`): the
  floor collapses to `0 ≤ rayleighOnVec (hubbardKinetic 1 0) …`. **Red 54 alone is not enough**
  — see Red 54b.
* **Red 54b (F4 at a nonzero diagonal `t`, distinct eigenvalues).** Same `M := 1`, `Ne := 2`,
  `hdown`/`hnum`/`hu0` as Red 54, but `t := Matrix.diagonal ![0, 1]` and `ε := ![0, 1]`: the
  floor is the strict nontrivial number `0 + 1 = 1` times `‖u‖²`. `hspec` here is genuinely
  earned (not the `ε := hT.eigenvalues` reflexivity shortcut of Red 24/54): it is derived from
  `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues` applied to the diagonal matrix's own
  characteristic-polynomial factorization (`Matrix.charpoly_diagonal`), so this is the Red that
  fails if the weights or the `hspec` multiset transport inside F4 are wrong.
* **Red 55 (the threshold is uniform in the system size and in `U`).** The capstone's own
  quantifier order, which no fixture-based test can reach: the model here cannot be a numeral
  fixture, because the density hypothesis `Ne/(N+1) ≤ ρ₁` refers to the *obtained* `ρ₁` and so
  forces `N` to be chosen after it (this is what `Tests.HubbardImpossibilityLowDensity`'s Red 2
  pins). Red 55 therefore pins the next best thing, and the one thing Red 1 misses.
-/

/-- **Red 45 (T1 pinned at `a = 2`, `b = 3`, `p = 1/3`).** -/
example :
    ∃ r : ℝ, 0 < r ∧ (3 : ℝ) * (r / 2) < 2 * (r / 2) ^ ((1 : ℝ) / 3) := by
  obtain ⟨r, hrpos, hr⟩ :=
    LatticeSystem.Math.exists_pos_forall_mul_lt_rpow (a := 2) (b := 3) (p := 1 / 3)
      (by norm_num) (by norm_num) (by norm_num)
  exact ⟨r, hrpos, hr (r / 2) (by linarith) (by linarith)⟩

/-- **Red 46 (the shared witness `r` applies at two distinct densities).** See the module-header
note above: the content guarded is the *sharing* of `r`, not a nonvacuous side condition. -/
example :
    ∃ r : ℝ, 0 < r ∧
      (3 : ℝ) * (r / 2) < 2 * (r / 2) ^ ((1 : ℝ) / 3) ∧
      (3 : ℝ) * (r / 4) < 2 * (r / 4) ^ ((1 : ℝ) / 3) := by
  obtain ⟨r, hrpos, hr⟩ :=
    LatticeSystem.Math.exists_pos_forall_mul_lt_rpow (a := 2) (b := 3) (p := 1 / 3)
      (by norm_num) (by norm_num) (by norm_num)
  exact ⟨r, hrpos, hr (r / 2) (by linarith) (by linarith),
    hr (r / 4) (by linarith) (by linarith)⟩

/-- **Red 47 (T1 at two different `(a, b)` pairs, the same `p`).** -/
example :
    (∃ r : ℝ, 0 < r ∧ (1 : ℝ) * (r / 2) < 1 * (r / 2) ^ ((1 : ℝ) / 2)) ∧
    (∃ r : ℝ, 0 < r ∧ (5 : ℝ) * (r / 2) < 7 * (r / 2) ^ ((1 : ℝ) / 2)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hrpos, hr⟩ :=
      LatticeSystem.Math.exists_pos_forall_mul_lt_rpow (a := 1) (b := 1) (p := 1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
    exact ⟨r, hrpos, hr (r / 2) (by linarith) (by linarith)⟩
  · obtain ⟨r, hrpos, hr⟩ :=
      LatticeSystem.Math.exists_pos_forall_mul_lt_rpow (a := 7) (b := 5) (p := 1 / 2)
        (by norm_num) (by norm_num) (by norm_num)
    exact ⟨r, hrpos, hr (r / 2) (by linarith) (by linarith)⟩

/-- **Red 51 (T1 pinned at `a = b = 1`, `p = 1/2`).** -/
example :
    ∃ r : ℝ, 0 < r ∧ (1 : ℝ) * (min r (1 / 4)) < 1 * (min r (1 / 4)) ^ ((1 : ℝ) / 2) := by
  obtain ⟨r, hrpos, hr⟩ := LatticeSystem.Math.exists_pos_forall_mul_lt_rpow
    (a := 1) (b := 1) (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨r, hrpos, hr (min r (1 / 4)) (lt_min hrpos (by norm_num)) (min_le_left r (1 / 4))⟩

/-- **Red 51 sharpness (`p = 1`, standalone).** References neither T1 nor any fixture: witnesses
that `hp1 : p < 1` is load-bearing, not decoration. -/
example : ¬ ((1 : ℝ) * 1 < 1 * (1 : ℝ) ^ (1 : ℝ)) := by
  rw [Real.rpow_one]; norm_num

/-- **Red 54 (F4 at `t = 0`, the degenerate floor).** -/
example :
    (0 : ℝ) * (star (hubbardAllUpState 1) ⬝ᵥ hubbardAllUpState 1).re
      ≤ rayleighOnVec (hubbardKinetic 1 (0 : Matrix (Fin 2) (Fin 2) ℂ))
        (hubbardAllUpState 1) := by
  have hk : (2 : ℕ) ≤ 1 + 1 := le_refl 2
  have hmono : Monotone (fun _ : Fin 2 => (0 : ℝ)) := fun _ _ _ => le_refl 0
  have heig : ∀ i : Fin 2, hT0.eigenvalues i = 0 := fun i => by
    rw [hT0.eigenvalues_eq]; simp [Matrix.zero_mulVec]
  have hspec : (Finset.univ : Finset (Fin 2)).val.map (fun _ : Fin 2 => (0 : ℝ))
      = (Finset.univ : Finset (Fin 2)).val.map hT0.eigenvalues := by
    have heq : hT0.eigenvalues = (fun _ : Fin 2 => (0 : ℝ)) := funext heig
    rw [heq]
  have h := LatticeSystem.Fermion.sum_lowestLevels_mul_le_rayleighOnVec_hubbardKinetic
    hT0 hk hmono hspec (hubbardAllUpState_ne_zero 1) allUpState_one_down_zero
    allUpState_one_number_two
  simpa using h

/-- Fixture: the diagonal Hermitian matrix `diag(0, 1)` on `Fin 2` (Red 54b). -/
private noncomputable def dfn : Fin 2 → ℂ := fun i => ((![0, 1] : Fin 2 → ℝ) i : ℂ)

/-- Fixture: `diag(0, 1)` is Hermitian, the hypothesis the floor lemma takes at Red 54b's nonzero
hopping. -/
private theorem hTdiag : (Matrix.diagonal dfn).IsHermitian :=
  Matrix.isHermitian_diagonal_iff.mpr fun i => by
    change star (dfn i) = dfn i
    rw [dfn]
    rw [Complex.star_def, Complex.conj_ofReal]

/-- Fixture: `hspec` for `diag(0, 1)`, earned via the characteristic-polynomial route rather than
the `ε := hT.eigenvalues` reflexivity shortcut, since Red 54b needs the ascending numeral function
`![0, 1]`, not `hTdiag.eigenvalues` itself. -/
private theorem hTdiag_eigenvalues :
    (Finset.univ : Finset (Fin 2)).val.map (![0, 1] : Fin 2 → ℝ)
      = (Finset.univ : Finset (Fin 2)).val.map hTdiag.eigenvalues := by
  have hroots : (Matrix.diagonal dfn).charpoly.roots = Multiset.map dfn Finset.univ.val := by
    rw [Matrix.charpoly_diagonal]
    rw [Polynomial.roots_prod]
    · simp
    · simp [Polynomial.X_sub_C_ne_zero]
  have heig := hTdiag.roots_charpoly_eq_eigenvalues
  rw [hroots] at heig
  have hcomp : Multiset.map dfn Finset.univ.val
      = Multiset.map Complex.ofReal (Multiset.map (![0, 1] : Fin 2 → ℝ) Finset.univ.val) := by
    rw [show dfn = Complex.ofReal ∘ (![0, 1] : Fin 2 → ℝ) from rfl, Multiset.map_map]
  have hcomp2 : Multiset.map (RCLike.ofReal ∘ hTdiag.eigenvalues) Finset.univ.val
      = Multiset.map Complex.ofReal (Multiset.map hTdiag.eigenvalues Finset.univ.val) := by
    rw [Multiset.map_map]
    rfl
  rw [hcomp, hcomp2] at heig
  exact (Multiset.map_injective Complex.ofReal_injective) heig

/-- **Red 54b (F4 at a nonzero diagonal `t`, distinct eigenvalues).** -/
example :
    (∑ i : Fin 2, (![0, 1] : Fin 2 → ℝ) i) * (star (hubbardAllUpState 1) ⬝ᵥ
        hubbardAllUpState 1).re
      ≤ rayleighOnVec (hubbardKinetic 1 (Matrix.diagonal dfn)) (hubbardAllUpState 1) := by
  have hk : (2 : ℕ) ≤ 1 + 1 := le_refl 2
  have hmono : Monotone (![0, 1] : Fin 2 → ℝ) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
      | exact absurd hab (by decide)
      | norm_num
  have h := LatticeSystem.Fermion.sum_lowestLevels_mul_le_rayleighOnVec_hubbardKinetic
    hTdiag hk hmono hTdiag_eigenvalues (hubbardAllUpState_ne_zero 1) allUpState_one_down_zero
    allUpState_one_number_two
  simpa using h

/-- **Red 55 (the density threshold is uniform in the system size and in `U`).** The witness `ρ₁`
is obtained *once* and then serves every system size, every hopping matrix and every interaction
strength: the goal keeps `∃ ρ₁` outside the `∀ N` and `∀ U`, so a hypothetical `∀ N, ∃ ρ₁, …`
reading could not discharge it. `Tests.HubbardImpossibilityLowDensity`'s Red 1 fixes `N` and `U`
before obtaining `ρ₁` and therefore cannot see this; yet it is the physical content of the
theorem, namely that the low-density regime does not shrink away as the volume grows. -/
example (c ρ₀ K : ℝ) (hc : 0 < c) (hρ₀ : 0 < ρ₀) (n₀ d : ℕ) (hd : 2 < d) :
    ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ ∀ (N Ne : ℕ) (U : ℝ) (t : Fin (N + 1) → Fin (N + 1) → ℂ)
      (ht : Matrix.IsHermitian t) (σ : Equiv.Perm (Fin (N + 1))) (ε : Fin (N + 1) → ℝ) (E₀ : ℂ),
      (∀ x : Fin (N + 1), ∑ y : Fin (N + 1), ‖t x y‖ ≤ K) → (∀ i j, t (σ i) (σ j) = t i j) →
      (∀ i j : Fin (N + 1), ∃ k : ℕ, (σ ^ k) i = j) → Monotone ε →
      Finset.univ.val.map ε = Finset.univ.val.map ht.eigenvalues →
      hubbardBandCondition ε c ρ₀ n₀ d → 2 ≤ Ne → 2 * n₀ ≤ Ne → (Ne : ℝ) / (N + 1) ≤ ρ₁ →
      0 ≤ U → hubbardEigenspaceAt t (U : ℂ) E₀ Ne ≠ ⊥ →
      (∀ E : ℂ, hubbardEigenspaceAt t (U : ℂ) E Ne ≠ ⊥ → E₀.re ≤ E.re) →
      ¬ ∀ v ∈ hubbardEigenspaceAt t (U : ℂ) E₀ Ne,
        (fermionTotalSpinSquared N).mulVec v = (((Ne : ℂ) / 2) * ((Ne : ℂ) / 2 + 1)) • v := by
  obtain ⟨ρ₁, hρ₁, h⟩ := hubbard_theorem_11_4 c ρ₀ K hc hρ₀ n₀ d hd
  exact ⟨ρ₁, hρ₁, fun N Ne U t ht σ ε E₀ hK htrans htransitive hmono hspec hband hNe2 hNen₀ hden
    hU hne hmin => h N t ht hK σ htrans htransitive ε hmono hspec hband Ne hNe2 hNen₀ hden U hU E₀
      hne hmin⟩

end LatticeSystem.Tests.HubbardImpossibilityLowDensityRoth
