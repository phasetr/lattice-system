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

open scoped BigOperators

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

end LatticeSystem.Tests.HubbardImpossibilityLowDensityRoth
