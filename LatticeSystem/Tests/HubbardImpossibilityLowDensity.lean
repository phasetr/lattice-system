import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensity
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardKineticSpinBounds
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardOnSiteInteractionSingleDown
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityTrial
import LatticeSystem.Fermion.JordanWigner.Hubbard.ChargesCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveCoeffAction
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedSectorGround
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import LatticeSystem.Math.MatrixAnalysis.CourantFischer
import LatticeSystem.Math.MatrixAnalysis.PermInvariantUniformEigenvector
import LatticeSystem.Math.MonotoneEnumeration
import Mathlib.Data.Matrix.PEquiv

/-!
# Test coverage for Theorem 11.4 (impossibility of ferromagnetism at low densities)

`hubbard_theorem_11_4` strengthens Tasaki's bare statement by a hopping scale `K` with its row-sum
bound `_hK` and a filling floor `_hNen₀`. These tests pin that signature and guard the two failure
modes of such added hypotheses:

- **Red 1**: an application test that consumes the theorem with every binder, including `_hK` and
  `_hNen₀`, so the arity and the position of `K` are pinned.
- **Red 2**: the filling hypotheses (`2 ≤ Ne`, `2 * n₀ ≤ Ne`, `Ne/(N+1) ≤ ρ₁`) are jointly
  satisfiable for every `ρ₁ > 0` and `n₀` — guards against under-quantification (vacuity).
- **Red 3**: every hopping matrix admits *some* uniform row-sum bound `K` — guards that
  `_hK` restricts only the order of quantifiers, never a single model.

The spin-resolved kinetic layer is covered by four further tests:

- **Red 4**: the `rfl` bridge. Pins `hubbardKinetic` as the `σ`-sum of `hubbardKineticSpin`, and
  that the `σ = 1` fiber really is the spin-**down** hopping term — a spin-tag flip that no type
  ever checks.
- **Red 5**: the consumption test for the Loewner bound `Ĥ^σ ≤ e·N̂_σ`; pins the exact
  `rayleighOnVec` shape the bound must produce, and that the site sum bridges to
  `fermionTotalDownNumber` definitionally.
- **Red 6**: the consumption test for the fully-polarized kill `Ĥ↓Φ = 0`; pins that the spin
  decomposition plus the kill collapse `hubbardKinetic` to its up-only fiber.
- **Red 7**: non-vacuity guard (mirrors Red 3) — every Hermitian matrix admits *some* uniform
  eigenvalue ceiling `e`, so the `∀ j, ε_j ≤ e` hypothesis restricts only the order of
  quantifiers, never a single model.

The `ν̂ = hubbardOnSiteInteraction _ 1` layer on the `N̂_↓ = 1` sector is covered by six further
tests:

- **Red 8**: the primary consumption test — for every `U`,
  `hubbardOnSiteInteraction_mulVec_sub_self_eq_zero_of_downNumber_one` collapses the Rayleigh
  quotient of the interaction on the Roth-projected vector to `0`.
- **Red 9**: meaning test / spin-tag guard — on the `M := 1` single-↓-electron fixture, `ν̂` sees
  zero doubly-occupied sites while `N̂_↓` sees exactly the one ↓ electron: pins that `ν̂` counts
  double occupancy, not ↓ occupancy (a swap that no type checks).
- **Red 10**: non-vacuity guard (mirrors Red 3/7) — the sector hypothesis `N̂_↓ v = v` is
  satisfiable by a *nonzero* vector (the same `M := 1` fixture), guarding against a vacuously-true
  sector hypothesis.
- **Red 11**: sharpness guard — on the `M := 1` fixture with **both** sites doubly occupied, `ν̂`
  is *not* idempotent (`ν̂(ν̂v) ≠ ν̂v`, the two coordinates being `4` and `2`): the project's
  recorded failure mode (an over-quantified statement false off the intended sector) written as a
  test rather than discovered in review.
- **Red 12**: the normalisation-shape consumption test —
  `dotProduct_star_self_sub_hubbardOnSiteInteraction_re_of_downNumber_one` consumed in the mixed
  `rayleighOnVec` form of (F.2).
- **Red 13**: the consumption test for sector closure —
  `fermionTotalDownNumber_mulVec_hubbardOnSiteInteraction_mulVec_of_downNumber_one` discharges the
  sector hypothesis for the doubly occupied part `ν̂v`, so the interaction vanishing re-applies to
  it; that re-application is how the energy split feeds `ν̂v` back into the sector lemmas.

The spin-flip trial state `Ψ = Ĉ†_↓(v)Φ↑` (Tasaki eq. (11.1.6)) and its Jordan–Wigner parity
factorisation are covered by six further tests, which pin `hubbardLowDensityTrialState`,
`fermionTotalDownNumber_mulVec_hubbardLowDensityTrialState`,
`hubbardLowDensityTrialState_ne_zero`, `dotProduct_fermionDownCreation_sandwich`,
`hubbardKinetic_mulVec_hubbardLowDensityTrialState`,
`hubbardKineticSpin_mul_spinfulCreationFromVector` and
`hubbardKineticSpin_commute_spinfulCreationFromVector_of_ne` at the shapes their consumers
require:

- **Red 14**: the primary PR-3→PR-4 junction — for the actual trial state `Ψ`, PR-3's interaction
  vanishing (`hubbardOnSiteInteraction_mulVec_sub_self_eq_zero_of_downNumber_one`) is fed by PR-4's
  `S1` (`Ψ` lies in the `N̂_↓ = 1` sector), for every `U`.
- **Red 15**: the parity/δ meaning test — the parity-factorisation sandwich at `X = 1` and `x ≠ y`
  collapses to `0`, pinning the Kronecker-δ shape of the sandwich.
- **Red 16**: the sharpness guard for the sandwich's own hypothesis — on an explicit `M := 1`
  configuration where `Φ'` already carries a ↓ electron at the creation site (violating the
  sandwich's `N̂_↓Φ' = 0` hypothesis), applying the ↓-creation again vanishes by Pauli exclusion
  while the value the sandwich formula predicts at `x = y` does not: `0 ≠ 1`. Unlike the other
  five tests here it is a **self-contained fixture** built from the ladder operators alone, so it
  exhibits the counterexample without consuming the sandwich itself.
- **Red 17**: non-vacuity guard (mirrors Red 3/7/10) — `S1`'s sector hypothesis is satisfied by a
  *nonzero* trial state (`v = Pi.single x 1`), so the one-↓ sector statements it feeds are not
  vacuous.
- **Red 18**: the kinetic consumption test — at `SUp = ∅` (so `Φ↑` is the vacuum and
  `occupiedEigenEnergy hT ∅ ∅ = 0`), `E`'s assembly collapses `Ĥ_kin Ψ` to `lam • Ψ` for an
  eigenvector `v` of `t`.
- **Red 19**: the spin-tag guard — `K1` at `σ = 1` (same spin as the trial state's ↓ creator,
  carrying the extra `Ĉ†(t·w)` term) pinned side by side with `K2` at `σ = 0, τ = 1` (cross spin,
  a plain commutator with no extra term); guards the `Fin 2` tag swap that no type catches.
-/

namespace LatticeSystem.Tests.HubbardImpossibilityLowDensity

open LatticeSystem.Fermion
open LatticeSystem.Quantum

/-- **Red 1.** Applying `hubbard_theorem_11_4` with its full signature: `K` in third position,
plus `hK` and `hNen₀`. -/
example (c ρ₀ K : ℝ) (hc : 0 < c) (hρ₀ : 0 < ρ₀) (n₀ d : ℕ) (hd : 2 < d)
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (ht : Matrix.IsHermitian t)
    (hK : ∀ x : Fin (N + 1), ∑ y : Fin (N + 1), ‖t x y‖ ≤ K)
    (σ : Equiv.Perm (Fin (N + 1))) (htrans : ∀ i j, t (σ i) (σ j) = t i j)
    (htransitive : ∀ i j : Fin (N + 1), ∃ k : ℕ, (σ ^ k) i = j)
    (ε : Fin (N + 1) → ℝ) (hmono : Monotone ε)
    (hspec : Finset.univ.val.map ε = Finset.univ.val.map ht.eigenvalues)
    (hband : hubbardBandCondition ε c ρ₀ n₀ d)
    (Ne : ℕ) (hNe2 : 2 ≤ Ne) (hNen₀ : 2 * n₀ ≤ Ne) (U : ℝ) (hU : 0 ≤ U) (E₀ : ℂ)
    (hne : hubbardEigenspaceAt t (U : ℂ) E₀ Ne ≠ ⊥)
    (hmin : ∀ E : ℂ, hubbardEigenspaceAt t (U : ℂ) E Ne ≠ ⊥ → E₀.re ≤ E.re) :
    ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ ((Ne : ℝ) / (N + 1) ≤ ρ₁ →
      ¬ ∀ v ∈ hubbardEigenspaceAt t (U : ℂ) E₀ Ne,
        (fermionTotalSpinSquared N).mulVec v
          = (((Ne : ℂ) / 2) * ((Ne : ℂ) / 2 + 1)) • v) := by
  obtain ⟨ρ₁, hρ₁, h⟩ := hubbard_theorem_11_4 c ρ₀ K hc hρ₀ n₀ d hd
  exact ⟨ρ₁, hρ₁, fun hden =>
    h N t ht hK σ htrans htransitive ε hmono hspec hband Ne hNe2 hNen₀ hden U hU E₀ hne hmin⟩

/-- **Red 2.** The filling hypotheses (`2 ≤ Ne`, `2 * n₀ ≤ Ne`, `Ne/(N+1) ≤ ρ₁`) are jointly
satisfiable for every `ρ₁ > 0` and `n₀`: guards against the *opposite* failure mode of adding
hypotheses (under-quantification / vacuity). -/
example (ρ₁ : ℝ) (hρ₁ : 0 < ρ₁) (n₀ : ℕ) :
    ∃ N Ne : ℕ, 2 ≤ Ne ∧ 2 * n₀ ≤ Ne ∧ (Ne : ℝ) / (N + 1) ≤ ρ₁ := by
  set Ne := max 2 (2 * n₀)
  obtain ⟨M, hM⟩ := exists_nat_gt ((Ne : ℝ) / ρ₁)
  refine ⟨M, Ne, le_max_left _ _, le_max_right _ _, ?_⟩
  have hM0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hM0]
  have hMNe : (Ne : ℝ) / ρ₁ < M := hM
  rw [div_lt_iff₀ hρ₁] at hMNe
  nlinarith [hMNe]

/-- **Red 3.** Every hopping matrix admits a uniform row-sum bound `K`: `_hK` restricts
only the order of quantifiers (`ρ₁` before `∀ t`), never a single model. -/
example (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    ∃ K : ℝ, ∀ x : Fin (N + 1), ∑ y : Fin (N + 1), ‖t x y‖ ≤ K := by
  exact ⟨Finset.univ.sup' Finset.univ_nonempty (fun x => ∑ y, ‖t x y‖),
    fun x => Finset.le_sup' (fun x => ∑ y, ‖t x y‖) (Finset.mem_univ x)⟩

/-- **Red 4a.** `hubbardKinetic` decomposes as the `σ`-sum of `hubbardKineticSpin`, and the
bridge is definitional. -/
example (t : Fin 2 → Fin 2 → ℂ) :
    hubbardKinetic 1 t = ∑ σ : Fin 2, hubbardKineticSpin 1 t σ := rfl

/-- **Red 4b.** The `σ = 1` fiber of `hubbardKineticSpin` really is the spin-**down** hopping
term (it would break if the spin tag were flipped, which no type ever checks). -/
example (t : Fin 2 → Fin 2 → ℂ) :
    hubbardKineticSpin 1 t 1
      = ∑ i : Fin 2, ∑ j : Fin 2, t i j • (fermionDownCreation 1 i * fermionDownAnnihilation 1 j) :=
  rfl

/-- **Red 5.** The consumption test for the Loewner bound `Ĥ^σ ≤ e·N̂_σ`: pins the exact
`rayleighOnVec` shape the bound must produce, and that the bound's site sum bridges to
`fermionTotalDownNumber` definitionally. -/
example {M : ℕ} {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian) (e : ℝ)
    (he : ∀ j : Fin (M + 1), hT.eigenvalues j ≤ e) (v : (Fin (2 * M + 2) → Fin 2) → ℂ) :
    rayleighOnVec (hubbardKineticSpin M t 1) v
      ≤ e * rayleighOnVec (fermionTotalDownNumber M) v := by
  have hbound := rayleighOnVec_mono (hubbardKineticSpin_le_smul_sum_spinSiteNumber hT 1 he) v
  rwa [rayleighOnVec_real_smul] at hbound

/-- **Red 6.** The consumption test for the fully-polarized kill `Ĥ↓Φ = 0`: the spin
decomposition plus the kill collapse `hubbardKinetic` to its up-only fiber. -/
example (M : ℕ) (t : Fin (M + 1) → Fin (M + 1) → ℂ) (Φ : (Fin (2 * M + 2) → Fin 2) → ℂ)
    (hΦ : (fermionTotalDownNumber M).mulVec Φ = 0) :
    (hubbardKinetic M t).mulVec Φ = (hubbardKineticSpin M t 0).mulVec Φ := by
  have hadd := hubbardKinetic_eq_hubbardKineticSpin_add M t
  have hdown := hubbardKineticSpin_one_mulVec_eq_zero_of_downNumber_zero M t hΦ
  rw [hadd, Matrix.add_mulVec, hdown, add_zero]

/-- **Red 7.** Non-vacuity guard (mirrors Red 3): every Hermitian matrix admits *some* uniform
eigenvalue ceiling `e`, so `∀ j, ε_j ≤ e` restricts only the order of quantifiers, never a single
model. -/
example {M : ℕ} {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian) :
    ∃ e : ℝ, ∀ j : Fin (M + 1), hT.eigenvalues j ≤ e :=
  ⟨Finset.univ.sup' Finset.univ_nonempty hT.eigenvalues,
    fun j => Finset.le_sup' hT.eigenvalues (Finset.mem_univ j)⟩

/-! ## The on-site interaction on the single-↓-electron sector -/

/-- Fixture for Red 9/Red 10: the `M := 1` configuration with one ↑ electron at site `0` and one
↓ electron at site `1` (built through `spinfulIndex`, never raw numerals). -/
private def hubbardOnSiteInteractionSingleDownConfig : Fin (2 * 1 + 2) → Fin 2 :=
  fun k => if k = spinfulIndex 1 0 0 ∨ k = spinfulIndex 1 1 1 then 1 else 0

/-- Fixture for Red 11: the `M := 1` configuration with **both** sites doubly occupied. -/
private def hubbardOnSiteInteractionDoublyOccupiedConfig : Fin (2 * 1 + 2) → Fin 2 :=
  fun _ => 1

/-- **Red 8.** Primary consumption test: for arbitrary `U`,
`hubbardOnSiteInteraction_mulVec_sub_self_eq_zero_of_downNumber_one` collapses the Rayleigh
quotient of the interaction on the Roth-projected vector to `0`. -/
example (M : ℕ) (U : ℂ) {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalDownNumber M).mulVec v = v) :
    rayleighOnVec (hubbardOnSiteInteraction M U)
        (v - (hubbardOnSiteInteraction M 1).mulVec v) = 0 := by
  unfold rayleighOnVec
  rw [hubbardOnSiteInteraction_mulVec_sub_self_eq_zero_of_downNumber_one M U hv,
    dotProduct_zero, Complex.zero_re]

/-- **Red 9.** Meaning test / spin-tag guard: on the single-↓-electron fixture, `ν̂` sees zero
doubly-occupied sites while `N̂_↓` sees exactly the one ↓ electron — pinning that `ν̂` counts
double occupancy, not ↓ occupancy (a swap that no type checks). -/
example :
    (hubbardOnSiteInteraction 1 1).mulVec (basisVec hubbardOnSiteInteractionSingleDownConfig)
        hubbardOnSiteInteractionSingleDownConfig = 0
      ∧ (fermionTotalDownNumber 1).mulVec (basisVec hubbardOnSiteInteractionSingleDownConfig)
            hubbardOnSiteInteractionSingleDownConfig
          = basisVec hubbardOnSiteInteractionSingleDownConfig
              hubbardOnSiteInteractionSingleDownConfig := by
  have h00 : hubbardOnSiteInteractionSingleDownConfig (spinfulIndex 1 0 0) = 1 := by decide
  have h01 : hubbardOnSiteInteractionSingleDownConfig (spinfulIndex 1 0 1) = 0 := by decide
  have h10 : hubbardOnSiteInteractionSingleDownConfig (spinfulIndex 1 1 0) = 0 := by decide
  have h11 : hubbardOnSiteInteractionSingleDownConfig (spinfulIndex 1 1 1) = 1 := by decide
  refine ⟨?_, ?_⟩
  · rw [show hubbardOnSiteInteraction 1 1 = hubbardOnSiteInteractionSite 1 (fun _ => 1) from rfl,
      hubbardOnSiteInteractionSite_mulVec_apply]
    have hweight : hubbardConfigInteractionWeight 1 (fun _ => (1 : ℂ))
        hubbardOnSiteInteractionSingleDownConfig = 0 := by
      unfold hubbardConfigInteractionWeight
      rw [Fin.sum_univ_two, h00, h01, h10, h11]
      norm_num
    rw [hweight, zero_mul]
  · rw [fermionTotalDownNumber_mulVec_apply, Fin.sum_univ_two, h01, h11]
    norm_num

/-- **Red 10.** Non-vacuity guard (mirrors Red 3/Red 7): the sector hypothesis `N̂_↓ v = v` is
satisfiable by a *nonzero* vector — the single-↓-electron fixture. Guards against a
vacuously-true sector hypothesis. -/
example :
    (fermionTotalDownNumber 1).mulVec (basisVec hubbardOnSiteInteractionSingleDownConfig)
        = basisVec hubbardOnSiteInteractionSingleDownConfig
      ∧ basisVec hubbardOnSiteInteractionSingleDownConfig
          hubbardOnSiteInteractionSingleDownConfig ≠ 0 := by
  have h01 : hubbardOnSiteInteractionSingleDownConfig (spinfulIndex 1 0 1) = 0 := by decide
  have h11 : hubbardOnSiteInteractionSingleDownConfig (spinfulIndex 1 1 1) = 1 := by decide
  refine ⟨?_, ?_⟩
  · rw [fermionTotalDownNumber_mulVec_basisVec, Fin.sum_univ_two, h01, h11]
    norm_num
  · rw [basisVec_self]
    exact one_ne_zero

/-- **Red 11.** Sharpness guard: the sector hypothesis is load-bearing. On the `M := 1`
configuration with **both** sites doubly occupied the two coordinates are `4` and `2`, and the
guard asserts their *inequality* outright, so `ν̂` is *not* idempotent there — the project's
recorded failure mode (an over-quantified statement false off the intended sector) written as a
test rather than discovered in review. -/
example :
    (hubbardOnSiteInteraction 1 1).mulVec
        ((hubbardOnSiteInteraction 1 1).mulVec
          (basisVec hubbardOnSiteInteractionDoublyOccupiedConfig))
        hubbardOnSiteInteractionDoublyOccupiedConfig = 4
      ∧ (hubbardOnSiteInteraction 1 1).mulVec
            (basisVec hubbardOnSiteInteractionDoublyOccupiedConfig)
            hubbardOnSiteInteractionDoublyOccupiedConfig = 2
      ∧ (hubbardOnSiteInteraction 1 1).mulVec
            ((hubbardOnSiteInteraction 1 1).mulVec
              (basisVec hubbardOnSiteInteractionDoublyOccupiedConfig))
            hubbardOnSiteInteractionDoublyOccupiedConfig
          ≠ (hubbardOnSiteInteraction 1 1).mulVec
              (basisVec hubbardOnSiteInteractionDoublyOccupiedConfig)
              hubbardOnSiteInteractionDoublyOccupiedConfig := by
  have hbridge : hubbardOnSiteInteraction 1 1
      = hubbardOnSiteInteractionSite 1 (fun _ => 1) := rfl
  have hweight : hubbardConfigInteractionWeight 1 (fun _ => (1 : ℂ))
      hubbardOnSiteInteractionDoublyOccupiedConfig = 2 := by
    unfold hubbardConfigInteractionWeight hubbardOnSiteInteractionDoublyOccupiedConfig
    rw [Fin.sum_univ_two]
    norm_num
  have hbasis :
      (hubbardOnSiteInteraction 1 1).mulVec
          (basisVec hubbardOnSiteInteractionDoublyOccupiedConfig)
          hubbardOnSiteInteractionDoublyOccupiedConfig = 2 := by
    rw [hbridge, hubbardOnSiteInteractionSite_mulVec_basisVec, hweight, Pi.smul_apply,
      basisVec_self, smul_eq_mul, mul_one]
  have hnu : (hubbardOnSiteInteraction 1 1).mulVec
      (basisVec hubbardOnSiteInteractionDoublyOccupiedConfig)
      = (2 : ℂ) • basisVec hubbardOnSiteInteractionDoublyOccupiedConfig := by
    rw [hbridge, hubbardOnSiteInteractionSite_mulVec_basisVec, hweight]
  have hsquare :
      (hubbardOnSiteInteraction 1 1).mulVec
          ((hubbardOnSiteInteraction 1 1).mulVec
            (basisVec hubbardOnSiteInteractionDoublyOccupiedConfig))
          hubbardOnSiteInteractionDoublyOccupiedConfig = 4 := by
    rw [hnu, hbridge, Matrix.mulVec_smul, hubbardOnSiteInteractionSite_mulVec_basisVec, hweight,
      Pi.smul_apply, Pi.smul_apply, basisVec_self, smul_eq_mul, smul_eq_mul, mul_one]
    norm_num
  refine ⟨hsquare, hbasis, ?_⟩
  rw [hsquare, hbasis]
  norm_num

/-- **Red 12.** Normalisation-shape consumption test:
`dotProduct_star_self_sub_hubbardOnSiteInteraction_re_of_downNumber_one` consumed in the mixed
`rayleighOnVec` form of (F.2). -/
example (M : ℕ) {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalDownNumber M).mulVec v = v) :
    (dotProduct (star (v - (hubbardOnSiteInteraction M 1).mulVec v))
        (v - (hubbardOnSiteInteraction M 1).mulVec v)).re
      = (dotProduct (star v) v).re - rayleighOnVec (hubbardOnSiteInteraction M 1) v := by
  unfold rayleighOnVec
  exact dotProduct_star_self_sub_hubbardOnSiteInteraction_re_of_downNumber_one M hv

/-- **Red 13.** Consumption test for sector closure: `N̂_↓(ν̂v) = ν̂v` is what lets the doubly
occupied part `ν̂v` be fed back into the sector lemmas, so here it discharges the sector hypothesis
of the interaction vanishing applied to `ν̂v` itself. It fails the moment
`fermionTotalDownNumber_mulVec_hubbardOnSiteInteraction_mulVec_of_downNumber_one` stops producing
the sector hypothesis in the shape the other lemmas consume. -/
example (M : ℕ) (U : ℂ) {v : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalDownNumber M).mulVec v = v) :
    rayleighOnVec (hubbardOnSiteInteraction M U)
        ((hubbardOnSiteInteraction M 1).mulVec v
          - (hubbardOnSiteInteraction M 1).mulVec ((hubbardOnSiteInteraction M 1).mulVec v))
      = 0 := by
  unfold rayleighOnVec
  rw [hubbardOnSiteInteraction_mulVec_sub_self_eq_zero_of_downNumber_one M U
      (fermionTotalDownNumber_mulVec_hubbardOnSiteInteraction_mulVec_of_downNumber_one M hv),
    dotProduct_zero, Complex.zero_re]

/-! ## The spin-flip trial state and its Jordan–Wigner parity factorisation (PR-4) -/

/-- **Red 14.** The primary PR-3→PR-4 junction: for the actual trial state
`Ψ = hubbardLowDensityTrialState e SUp v`, PR-3's interaction vanishing is fed by PR-4's `S1`
(`fermionTotalDownNumber_mulVec_hubbardLowDensityTrialState`), for every `U`. Pins that `S1`
delivers the sector hypothesis in exactly the shape the interaction vanishing consumes. -/
example {M : ℕ} (U : ℂ) (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (SUp : Finset (Fin (M + 1))) (v : Fin (M + 1) → ℂ) :
    (hubbardOnSiteInteraction M U).mulVec
        (hubbardLowDensityTrialState e SUp v
          - (hubbardOnSiteInteraction M 1).mulVec (hubbardLowDensityTrialState e SUp v))
      = 0 :=
  hubbardOnSiteInteraction_mulVec_sub_self_eq_zero_of_downNumber_one M U
    (fermionTotalDownNumber_mulVec_hubbardLowDensityTrialState e SUp v)

/-- **Red 15.** Parity/δ meaning test: the sandwich `B`
(`dotProduct_fermionDownCreation_sandwich`) at `X = 1` and `x ≠ y` collapses to `0`, pinning the
Kronecker-δ shape of its conclusion. -/
example (M : ℕ) {Φ Φ' : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hΦ' : (fermionTotalDownNumber M).mulVec Φ' = 0) {x y : Fin (M + 1)} (hxy : x ≠ y) :
    dotProduct (star ((fermionDownCreation M y).mulVec Φ))
        ((1 : ManyBodyOp (Fin (2 * M + 2))).mulVec ((fermionDownCreation M x).mulVec Φ'))
      = 0 := by
  rw [dotProduct_fermionDownCreation_sandwich (1 : ManyBodyOp (Fin (2 * M + 2)))
      (fun z => Commute.one_left _) hΦ' x y, if_neg hxy, zero_mul]

/-- Fixture for Red 16: the `M := 1` configuration with a single ↓ electron already at site `0` —
this violates the sandwich `B`'s hypothesis `N̂_↓Φ' = 0`. -/
private def hubbardImpossibilityLowDensitySharpnessConfig : Fin (2 * 1 + 2) → Fin 2 :=
  fun k => if k = spinfulIndex 1 0 1 then 1 else 0

/-- **Red 16.** Sharpness guard for the sandwich's own hypothesis. On the fixture above, applying
the ↓-creation operator again at the already-occupied site vanishes by Pauli exclusion, so the
sandwich value is `0`; but the value the sandwich formula predicts at `x = y` (`⟨Φ',Φ'⟩`) is `1`.
`0 ≠ 1`: the `N̂_↓Φ' = 0` hypothesis cannot be dropped. The fixture is self-contained — it uses
the ladder operators alone, not the sandwich. -/
example :
    (fermionTotalDownNumber 1).mulVec (basisVec hubbardImpossibilityLowDensitySharpnessConfig)
        = basisVec hubbardImpossibilityLowDensitySharpnessConfig
      ∧ dotProduct
          (star ((fermionDownCreation 1 0).mulVec
              (basisVec hubbardImpossibilityLowDensitySharpnessConfig)))
          ((1 : ManyBodyOp (Fin (2 * 1 + 2))).mulVec
              ((fermionDownCreation 1 0).mulVec
                (basisVec hubbardImpossibilityLowDensitySharpnessConfig)))
        ≠ dotProduct (star (basisVec hubbardImpossibilityLowDensitySharpnessConfig))
            ((1 : ManyBodyOp (Fin (2 * 1 + 2))).mulVec
                (basisVec hubbardImpossibilityLowDensitySharpnessConfig)) := by
  have hocc : hubbardImpossibilityLowDensitySharpnessConfig (spinfulIndex 1 0 1) = 1 := by decide
  have hocc1 : hubbardImpossibilityLowDensitySharpnessConfig (spinfulIndex 1 1 1) = 0 := by decide
  have hcreate : (fermionDownCreation 1 0).mulVec
      (basisVec hubbardImpossibilityLowDensitySharpnessConfig) = 0 := by
    rw [show fermionDownCreation 1 0 = fermionMultiCreation (2 * 1 + 1) (spinfulIndex 1 0 1)
        from rfl, fermionMultiCreation_mulVec_basisVec, if_neg (by rw [hocc]; decide)]
  have hlhs : dotProduct
      (star ((fermionDownCreation 1 0).mulVec
          (basisVec hubbardImpossibilityLowDensitySharpnessConfig)))
      ((1 : ManyBodyOp (Fin (2 * 1 + 2))).mulVec
          ((fermionDownCreation 1 0).mulVec
            (basisVec hubbardImpossibilityLowDensitySharpnessConfig))) = 0 := by
    rw [hcreate, Matrix.mulVec_zero, star_zero, dotProduct_zero]
  have hrhs : dotProduct (star (basisVec hubbardImpossibilityLowDensitySharpnessConfig))
      ((1 : ManyBodyOp (Fin (2 * 1 + 2))).mulVec
          (basisVec hubbardImpossibilityLowDensitySharpnessConfig)) = 1 := by
    rw [basisVec_expectation_eq_diagonal, Matrix.one_apply_eq]
  refine ⟨?_, ?_⟩
  · rw [fermionTotalDownNumber_mulVec_basisVec, Fin.sum_univ_two, hocc, hocc1]
    norm_num
  · rw [hlhs, hrhs]
    norm_num

/-- **Red 17.** Non-vacuity guard (mirrors Red 3/7/10): `S1`'s sector hypothesis is satisfied by a
*nonzero* trial state, `v = Pi.single x 1`. Pins `S1` and `hubbardLowDensityTrialState_ne_zero`
side by side, so the one-↓ sector statements they feed are not vacuous. -/
example {M : ℕ} (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ))
    (SUp : Finset (Fin (M + 1))) (x : Fin (M + 1)) :
    (fermionTotalDownNumber M).mulVec (hubbardLowDensityTrialState e SUp (Pi.single x (1 : ℂ)))
        = hubbardLowDensityTrialState e SUp (Pi.single x (1 : ℂ))
      ∧ hubbardLowDensityTrialState e SUp (Pi.single x (1 : ℂ)) ≠ 0 := by
  refine ⟨fermionTotalDownNumber_mulVec_hubbardLowDensityTrialState e SUp (Pi.single x 1), ?_⟩
  refine hubbardLowDensityTrialState_ne_zero e SUp (fun h => ?_)
  have := congrFun h x
  simp at this

/-- **Red 18.** Kinetic consumption test: at `SUp = ∅` (so `Φ↑` is the vacuum and
`occupiedEigenEnergy hT ∅ ∅ = 0`), the assembly `E`
(`hubbardKinetic_mulVec_hubbardLowDensityTrialState`) collapses `Ĥ_kin Ψ` to `lam • Ψ` for an
eigenvector `v` of `t`.  This pins the eigenvalue slot in the `SUp = ∅` base case only: the
occupied-energy offset vanishes there, so its behaviour for nonempty `SUp` is untested. -/
example {M : ℕ} {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    {v : Fin (M + 1) → ℂ} {lam : ℂ} (hv : t.mulVec v = lam • v) :
    (hubbardKinetic M t).mulVec (hubbardLowDensityTrialState (eigenbasisAsBasis hT) ∅ v)
      = lam • hubbardLowDensityTrialState (eigenbasisAsBasis hT) ∅ v := by
  have hE := hubbardKinetic_mulVec_hubbardLowDensityTrialState hT ∅ hv
  simpa [occupiedEigenEnergy, Finset.sum_empty, zero_add] using hE

/-- **Red 19.** Spin-tag guard: `K1` (`hubbardKineticSpin_mul_spinfulCreationFromVector`) at
`σ = 1` (same spin as the trial state's ↓ creator, carrying the extra `Ĉ†(t·w)` term) pinned side
by side with `K2` (`hubbardKineticSpin_commute_spinfulCreationFromVector_of_ne`) at `σ = 0, τ = 1`
(cross spin, a plain commutator with no extra term); guards the `Fin 2` tag swap that no type
catches. -/
example {M : ℕ} (t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (w : Fin (M + 1) → ℂ) :
    hubbardKineticSpin M t 1 * spinfulCreationFromVector M w 1
        = spinfulCreationFromVector M w 1 * hubbardKineticSpin M t 1
          + spinfulCreationFromVector M (t.mulVec w) 1
      ∧ hubbardKineticSpin M t 0 * spinfulCreationFromVector M w 1
          = spinfulCreationFromVector M w 1 * hubbardKineticSpin M t 0 :=
  ⟨hubbardKineticSpin_mul_spinfulCreationFromVector M t w 1,
    (hubbardKineticSpin_commute_spinfulCreationFromVector_of_ne M t w
      (by decide : (0 : Fin 2) ≠ 1)).eq⟩

/-!
## Theorem 11.4 PR-5 — translation invariance and the delocalised lowest eigenmode

The eight Reds below pin the four PR-5 declarations of
`LatticeSystem/Math/MatrixAnalysis/PermInvariantUniformEigenvector.lean`
(`commute_toPEquiv_toMatrix_of_perm_invariant`,
`norm_apply_eq_norm_apply_of_comp_perm_smul`, `eigenspace_mulVecLin_ne_bot_of_map_eq`,
`exists_uniformModulus_eigenvector_of_transitive_perm_invariance`).  Reds 20/21/21b consume the
capstone A4 — its
normalisation at two sizes, then its eigen-equation on a non-diagonal matrix at a nonzero
eigenvalue; Reds 23/23b pin A1 and the failure of A1's hypothesis; Red 24 pins A3 and Red 25 pins
A2 in isolation.  Red 22 alone references none of the four: it is the standalone sharpness
counterexample, built from existing mathlib API, showing `_htransitive` cannot be dropped from A4.
-/

/-- **Red 20.** Application-shape / non-vacuity guard for A4 at `M = 1`. With `σ = Equiv.swap 0 1`
and `t = 0`, `htrans` and `htransitive` hold trivially and the eigenspace at `lam = 0` is `⊤ ≠ ⊥`
(witnessed by `Pi.single 0 1`); A4 then returns some `v` whose normalisation
`∑ x, ‖v x‖ ^ 2 = 1` is the consequence pinned here (an off-by-one in the `1 / card n` constant
would give `2` instead). -/
example :
    ∃ v : Fin 2 → ℂ, (0 : Matrix (Fin 2) (Fin 2) ℂ).mulVec v = (0 : ℂ) • v
      ∧ ∑ x, ‖v x‖ ^ 2 = 1 := by
  have htrans : ∀ i j : Fin 2,
      (0 : Matrix (Fin 2) (Fin 2) ℂ) (Equiv.swap (0 : Fin 2) 1 i) (Equiv.swap (0 : Fin 2) 1 j)
        = (0 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    intro i j; simp
  have htransitive : ∀ i j : Fin 2, ∃ k : ℕ, ((Equiv.swap (0 : Fin 2) 1) ^ k) i = j := by
    intro i j; fin_cases i <;> fin_cases j <;> first | exact ⟨0, rfl⟩ | exact ⟨1, by decide⟩
  have hlam : Module.End.eigenspace (0 : Matrix (Fin 2) (Fin 2) ℂ).mulVecLin (0 : ℂ) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨Pi.single 0 1, ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]; simp
    · intro h
      have := congrFun h 0
      simp at this
  obtain ⟨v, hv, hmod⟩ :=
    LatticeSystem.Math.exists_uniformModulus_eigenvector_of_transitive_perm_invariance
      htrans htransitive hlam
  refine ⟨v, hv, ?_⟩
  simp only [hmod]
  simp

/-- **Red 21.** Size dependence of A4's constant: at `M = 2` (`σ = finRotate 3`), the returned
eigenvector satisfies `∀ x, ‖v x‖ ^ 2 = 1 / 3`, pinning `1 / (M + 1)` against a coincidence at
`M = 1` (Red 20). -/
example :
    ∃ v : Fin 3 → ℂ, (0 : Matrix (Fin 3) (Fin 3) ℂ).mulVec v = (0 : ℂ) • v
      ∧ ∀ x, ‖v x‖ ^ 2 = 1 / 3 := by
  have htrans : ∀ i j : Fin 3,
      (0 : Matrix (Fin 3) (Fin 3) ℂ) (finRotate 3 i) (finRotate 3 j)
        = (0 : Matrix (Fin 3) (Fin 3) ℂ) i j := by
    intro i j; simp
  have htransitive : ∀ i j : Fin 3, ∃ k : ℕ, ((finRotate 3) ^ k) i = j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      first | exact ⟨0, rfl⟩ | exact ⟨1, by decide⟩ | exact ⟨2, by decide⟩
  have hlam : Module.End.eigenspace (0 : Matrix (Fin 3) (Fin 3) ℂ).mulVecLin (0 : ℂ) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨Pi.single 0 1, ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]; simp
    · intro h
      have := congrFun h 0
      simp at this
  obtain ⟨v, hv, hmod⟩ :=
    LatticeSystem.Math.exists_uniformModulus_eigenvector_of_transitive_perm_invariance
      htrans htransitive hlam
  exact ⟨v, hv, fun x => by simpa using hmod x⟩

/-- **Red 21b (A4's eigen-equation exercised).** Reds 20/21 run A4 at `t = 0`, `lam = 0`, where the
eigen-equation `0 = 0 • v` holds for every `v`; here `t = ![![0, 1], ![1, 0]]` is swap-invariant
but not diagonal and `lam = 1` is a genuine eigenvalue (eigenspace spanned by `![1, 1]`), so the
returned `v` has to satisfy `t.mulVec v = 1 • v` — whence `v 1 = v 0` — on top of the uniform
modulus. -/
example :
    ∃ v : Fin 2 → ℂ, (Matrix.of ![![(0 : ℂ), 1], ![1, 0]]).mulVec v = (1 : ℂ) • v
      ∧ v 1 = v 0 ∧ ∀ x, ‖v x‖ ^ 2 = 1 / 2 := by
  have htrans : ∀ i j : Fin 2,
      (Matrix.of ![![(0 : ℂ), 1], ![1, 0]]) (Equiv.swap (0 : Fin 2) 1 i)
          (Equiv.swap (0 : Fin 2) 1 j)
        = (Matrix.of ![![(0 : ℂ), 1], ![1, 0]]) i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp
  have htransitive : ∀ i j : Fin 2, ∃ k : ℕ, ((Equiv.swap (0 : Fin 2) 1) ^ k) i = j := by
    intro i j; fin_cases i <;> fin_cases j <;> first | exact ⟨0, rfl⟩ | exact ⟨1, by decide⟩
  have hlam : Module.End.eigenspace
      (Matrix.of ![![(0 : ℂ), 1], ![1, 0]]).mulVecLin (1 : ℂ) ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨![1, 1], ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      funext x
      fin_cases x <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · intro h
      have := congrFun h 0
      simp at this
  obtain ⟨v, hv, hmod⟩ :=
    LatticeSystem.Math.exists_uniformModulus_eigenvector_of_transitive_perm_invariance
      htrans htransitive hlam
  refine ⟨v, hv, ?_, fun x => by simpa using hmod x⟩
  have hv0 := congrFun hv 0
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hv0

/-- **Red 22 (sharpness of `_htransitive`).** With `σ = 1` (the identity), `htrans` holds for
*every* matrix `t` — in particular for `t = Matrix.diagonal ![0, 1]` at `lam = 0` — so if the
transitivity hypothesis were droppable from A4, every `0`-eigenvector of this `t` would have
constant modulus `1/2`. It does not: the eigen-equation forces `v 1 = 0`, and `‖v 1‖ ^ 2 = 0 ≠ 1/2`.
This is a standalone counterexample using only existing mathlib API (no reference to A4),
witnessing that `_htransitive` is load-bearing and not decoration. -/
example :
    ∀ v : Fin 2 → ℂ, (Matrix.diagonal ![(0 : ℂ), 1]).mulVec v = (0 : ℂ) • v →
      ¬ (∀ x, ‖v x‖ ^ 2 = 1 / 2) := by
  intro v hv hcontra
  have h1 : v 1 = 0 := by
    have hcongr := congrFun hv 1
    rw [Matrix.mulVec_diagonal] at hcongr
    simpa using hcongr
  have := hcontra 1
  rw [h1] at this
  norm_num at this

/-- **Red 23 (A1 pinned).** `commute_toPEquiv_toMatrix_of_perm_invariant` applied to a genuinely
swap-invariant `t = ![![a, b], ![b, a]]` (with `a = 1`, `b = 2`) gives the commutation
`P_σ · t = t · P_σ`. -/
example :
    Commute ((Equiv.swap (0 : Fin 2) 1).toPEquiv.toMatrix : Matrix (Fin 2) (Fin 2) ℂ)
      (Matrix.of ![![(1 : ℂ), 2], ![2, 1]]) :=
  LatticeSystem.Math.commute_toPEquiv_toMatrix_of_perm_invariant
    (fun i j => by fin_cases i <;> fin_cases j <;> simp)

/-- **Red 23b (A1's hypothesis pinned).** `htrans` itself *fails* for
`t = Matrix.diagonal ![0, 1]` under `σ = Equiv.swap 0 1` — pinning that A1's hypothesis is the
invariance condition and not something weaker (a reviewer's first question about A1). -/
example :
    ¬ (∀ i j : Fin 2,
        (Matrix.diagonal ![(0 : ℂ), 1]) (Equiv.swap (0 : Fin 2) 1 i)
            (Equiv.swap (0 : Fin 2) 1 j)
          = (Matrix.diagonal ![(0 : ℂ), 1]) i j) := by
  intro h
  have := h 0 0
  simp [Equiv.swap_apply_left, Matrix.diagonal_apply_eq] at this

/-- **Red 24 (A3 pinned).** On the `1 × 1` zero matrix (trivially Hermitian), taking
`ε := hT.eigenvalues` makes `hspec` the reflexive multiset equality, and
`eigenspace_mulVecLin_ne_bot_of_map_eq` must still deliver a non-trivial eigenspace at `ε 0`. -/
example :
    Module.End.eigenspace (0 : Matrix (Fin 1) (Fin 1) ℂ).mulVecLin
        (((Matrix.isHermitian_zero (n := Fin 1) (α := ℂ)).eigenvalues 0 : ℝ) : ℂ)
      ≠ ⊥ :=
  LatticeSystem.Math.eigenspace_mulVecLin_ne_bot_of_map_eq
    (t := (0 : Matrix (Fin 1) (Fin 1) ℂ)) (Matrix.isHermitian_zero (n := Fin 1) (α := ℂ))
    (ε := (Matrix.isHermitian_zero (n := Fin 1) (α := ℂ)).eigenvalues) rfl 0

/-- **Red 25 (A2 pinned in isolation).** Concrete `w = ![1, -1]`, `σ = Equiv.swap 0 1`, `μ = -1`
(deliberately not `1`, so the proof cannot silently assume the phase is trivial) satisfy
`w ∘ σ = μ • w`; A2 must conclude `‖w 0‖ = ‖w 1‖`. -/
example :
    ‖(![(1 : ℂ), -1] : Fin 2 → ℂ) 0‖ = ‖(![(1 : ℂ), -1] : Fin 2 → ℂ) 1‖ := by
  set w : Fin 2 → ℂ := ![1, -1] with hw_def
  have hw : w ∘ (Equiv.swap (0 : Fin 2) 1) = (-1 : ℂ) • w := by
    funext x; fin_cases x <;> simp [hw_def]
  have hne : w ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [hw_def] at this
  have htransitive : ∀ i j : Fin 2, ∃ k : ℕ, ((Equiv.swap (0 : Fin 2) 1) ^ k) i = j := by
    intro i j; fin_cases i <;> fin_cases j <;> first | exact ⟨0, rfl⟩ | exact ⟨1, by decide⟩
  exact LatticeSystem.Math.norm_apply_eq_norm_apply_of_comp_perm_smul hw hne htransitive 0 1

/-!
## Theorem 11.4 PR-5b — the single-particle spectrum enumeration bridge

The six Reds below cover `LatticeSystem/Math/MonotoneEnumeration.lean`. Three of its declarations
are referenced directly: `eq_comp_sort_of_monotone_of_map_eq` = C1 (Red 26),
`exists_lowestLevels_finset_of_map_eq` = C3 (Reds 28 and 31), `sum_lowestLevels_succ` = C5
(Red 29). Red 27 reads against the weighted lemmas W1 (`sum_lowestLevels_le_sum_weighted`) and W2
(`sum_lowestLevels_le_sum_weighted_of_map_eq`, pinned separately in the PR-7b section of
`LatticeSystem.Tests.HubbardImpossibilityLowDensityRoth`), on
the same fixture. Red 30 is the standalone sharpness counterexample for `hmono`, read against
W2, and
references neither C1/C3/C5 nor W1/W2. The primary fixture for
Reds 26/28/29/31 is `m = 3`, `α = ℕ`, `ε := ![0, 1, 2]`, `g := ![2, 0, 1]`, chosen so
`hspec`/`hmono`/every concrete sum is `decide`-able; Red 27 restates the same values over `ℝ`
(`decide` does not reduce on `ℝ`, so `ε := fun i => (i : ℝ)` for a computable `Monotone` proof and
`g := ![2, 0, 1] : Fin 3 → ℝ`, with `hspec` via `List.rotate_perm` rather than `decide`), since
W1/W2 are stated over `ℝ`. Red 31 is the junction guard
at the real consumer's types (`Matrix.IsHermitian.eigenvalues` / `occupiedEigenEnergy`).
-/

/-- **Red 26 (C1 pinned).** On the fixture, `ε = g ∘ Tuple.sort g`. Guards the direction of the
`Multiset.map` hypothesis: an inverted `hspec` still typechecks (the same trap Red 24 guards for
A3). -/
example :
    (![0, 1, 2] : Fin 3 → ℕ)
      = (![2, 0, 1] : Fin 3 → ℕ) ∘ Tuple.sort (![2, 0, 1] : Fin 3 → ℕ) := by
  have hmono : Monotone (![0, 1, 2] : Fin 3 → ℕ) := by decide
  have hspec : (Finset.univ : Finset (Fin 3)).val.map (![0, 1, 2] : Fin 3 → ℕ)
      = (Finset.univ : Finset (Fin 3)).val.map (![2, 0, 1] : Fin 3 → ℕ) := by decide
  exact LatticeSystem.Math.eq_comp_sort_of_monotone_of_map_eq hmono hspec

/-- **Red 27 (W2 pinned, with the inequality direction — retargeted from the deleted C4).**
`k = 2`, `w := ![1, 0, 1] : Fin 3 → ℝ` (the indicator of `S = {0, 2}`, so `∑ j, g j * w j
= g 0 + g 2 = 3`), while `∑ i : Fin 2, ε (castLE _ i) = 1`. Asserts the *consequence* `1 ≤ 3`
obtained through W2 (`sum_lowestLevels_le_sum_weighted_of_map_eq`, the successor of the deleted
`sum_lowestLevels_le_sum_of_map_eq` = C4), so a flipped inequality fails to compile. The `{0,
1}`-valued `w` reproduces C4's original `S`-indicator consumption exactly, so the sharpness
coverage C4 provided does not decrease after its deletion. -/
example : (1 : ℝ) ≤ 3 := by
  have hmono : Monotone (fun i : Fin 3 => (i : ℝ)) := fun a b hab => by
    change (a : ℝ) ≤ (b : ℝ)
    have h : (a : ℕ) ≤ (b : ℕ) := hab
    exact_mod_cast h
  have hspec : (Finset.univ : Finset (Fin 3)).val.map (fun i : Fin 3 => (i : ℝ))
      = (Finset.univ : Finset (Fin 3)).val.map (![2, 0, 1] : Fin 3 → ℝ) := by
    rw [Fin.univ_val_map, Fin.univ_val_map]
    have hofFnε : List.ofFn (fun i : Fin 3 => (i : ℝ)) = [0, 1, 2] := by
      simp [List.ofFn_succ, List.ofFn_zero]
      norm_num
    have hofFng : List.ofFn (![2, 0, 1] : Fin 3 → ℝ) = [2, 0, 1] := by
      simp [List.ofFn_succ, List.ofFn_zero]
    rw [hofFnε, hofFng]
    have hrot : ([0, 1, 2] : List ℝ).rotate 2 = [2, 0, 1] := by rfl
    exact Multiset.coe_eq_coe.mpr (hrot ▸ (List.rotate_perm ([0, 1, 2] : List ℝ) 2).symm)
  have hk : (2 : ℕ) ≤ 3 := by decide
  set w : Fin 3 → ℝ := ![1, 0, 1] with hw_def
  have hw0 : ∀ j, 0 ≤ w j := fun j => by fin_cases j <;> norm_num [hw_def]
  have hw1 : ∀ j, w j ≤ 1 := fun j => by fin_cases j <;> norm_num [hw_def]
  have hsum : ∑ j, w j = (2 : ℕ) := by
    change (∑ j, w j : ℝ) = 2
    simp [hw_def, Fin.sum_univ_three]
    norm_num
  have h := LatticeSystem.Math.sum_lowestLevels_le_sum_weighted_of_map_eq hk hmono hspec hw0 hw1
    hsum
  have hlhs : (∑ i : Fin 2, (fun i : Fin 3 => (i : ℝ)) (Fin.castLE hk i)) = 1 := by
    simp [Fin.sum_univ_two]
  have hrhs : (∑ j : Fin 3, (![2, 0, 1] : Fin 3 → ℝ) j * w j) = 3 := by
    simp [hw_def, Fin.sum_univ_three]
    norm_num
  rw [hlhs, hrhs] at h
  exact h

/-- **Red 28 (C3 pinned, non-vacuity of "lowest").** Obtains `S` from C3 at `k = 2` and asserts
`S.card = 2 ∧ ∑ p ∈ S, g p = 1`. The value `1` (not `3`) is the guard that C3 really returns the
*lowest* levels rather than an arbitrary 2-subset — the single most likely silent bug. -/
example :
    ∃ S : Finset (Fin 3), S.card = 2 ∧ ∑ p ∈ S, (![2, 0, 1] : Fin 3 → ℕ) p = 1 := by
  have hmono : Monotone (![0, 1, 2] : Fin 3 → ℕ) := by decide
  have hspec : (Finset.univ : Finset (Fin 3)).val.map (![0, 1, 2] : Fin 3 → ℕ)
      = (Finset.univ : Finset (Fin 3)).val.map (![2, 0, 1] : Fin 3 → ℕ) := by decide
  have hk : (2 : ℕ) ≤ 3 := by decide
  obtain ⟨S, hScard, hSsum⟩ :=
    LatticeSystem.Math.exists_lowestLevels_finset_of_map_eq hk hmono hspec
  refine ⟨S, hScard, ?_⟩
  have hrhs : (∑ i : Fin 2, (![0, 1, 2] : Fin 3 → ℕ) (Fin.castLE hk i)) = 1 := by
    simp [Fin.sum_univ_succ]
  rw [hSsum, hrhs]

/-- **Red 29 (C5 pinned, off-by-one).** `∑ i : Fin 3, ε (castLE _ i)
= (∑ i : Fin 2, ε (castLE _ i)) + ε 2`, i.e. `3 = 1 + 2`. A `Fin.last`/`castSucc` slip would give
`1 + 1` or `3 + 2`. -/
example : (3 : ℕ) = 1 + 2 := by
  have hk : (2 : ℕ) + 1 ≤ 3 := le_refl 3
  have h := LatticeSystem.Math.sum_lowestLevels_succ (ε := (![0, 1, 2] : Fin 3 → ℕ)) hk
  have hlhs : (∑ i : Fin 3, (![0, 1, 2] : Fin 3 → ℕ) (Fin.castLE hk i)) = 3 := by
    simp [Fin.sum_univ_succ]
  have hrhs1 : (∑ i : Fin 2, (![0, 1, 2] : Fin 3 → ℕ)
      (Fin.castLE (Nat.le_of_succ_le hk) i)) = 1 := by
    simp [Fin.sum_univ_succ]
  have hrhs2 : (![0, 1, 2] : Fin 3 → ℕ) ⟨2, hk⟩ = 2 := by simp
  -- `rewrite`, not `rw`: the latter's trailing `rfl` would close the goal on its own and the
  -- rewritten `h` would no longer be what discharges it.
  rewrite [hlhs, hrhs1, hrhs2] at h
  exact h

/-- **Red 30 (sharpness of `hmono` — the load-bearing hypothesis, read against W2).** Standalone,
using none of C1/C3/C5 or W1/W2. With `ε := ![2, 0, 1]` and `g := ε` (so `hspec` is `rfl` and
monotonicity fails), `k = 1`, `S = {1}`: `∑ i : Fin 1, ε (castLE _ i) = 2` but `∑ p ∈ S, g p = 0`,
so the unweighted specialisation of W2's conclusion (the deleted C4's statement) is *false* without
`Monotone ε`. Mirrors Red 22's discipline and is the test a reviewer will ask for. -/
example :
    ¬ (∑ i : Fin 1, (![2, 0, 1] : Fin 3 → ℕ) (Fin.castLE (by decide : (1 : ℕ) ≤ 3) i)
        ≤ ∑ p ∈ ({1} : Finset (Fin 3)), (![2, 0, 1] : Fin 3 → ℕ) p) := by
  have hlhs : (∑ i : Fin 1, (![2, 0, 1] : Fin 3 → ℕ) (Fin.castLE (by decide : (1 : ℕ) ≤ 3) i))
      = 2 := by decide
  have hrhs : (∑ p ∈ ({1} : Finset (Fin 3)), (![2, 0, 1] : Fin 3 → ℕ) p) = 0 := by decide
  rw [hlhs, hrhs]
  decide

/-- **Red 31 (application shape at the real consumer's types).** Instantiates C3 with
`g := hT.eigenvalues` for `hT : (0 : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian` and `ε := 0` (`hspec`
by rewriting `hT.eigenvalues = 0`, itself obtained from `Matrix.IsHermitian.eigenvalues_eq` and
`Matrix.zero_mulVec`), then feeds the returned `S : Finset (Fin 2)` to `occupiedEigenEnergy hT S ∅`
and asserts it is `0`. This is the junction guard for the argument *type*: it pins that the
`Finset (Fin (M+1))` produced by the generic `Math/` layer is literally what the Fermion layer
takes. The arc's remaining junction obligations — securing `Ne ≤ N + 1` and obtaining
`hspec`/`hmono` at the genuine eigenvalues — are not exercised here and first arise in PR-7. -/
example {hT : (0 : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian} :
    ∃ S : Finset (Fin 2), S.card = 1 ∧ occupiedEigenEnergy hT S ∅ = 0 := by
  have heig : ∀ i, hT.eigenvalues i = 0 := fun i => by
    rw [hT.eigenvalues_eq]; simp [Matrix.zero_mulVec]
  have hε : hT.eigenvalues = (0 : Fin 2 → ℝ) := funext heig
  have hmono : Monotone (0 : Fin 2 → ℝ) := monotone_const
  have hspec : (Finset.univ : Finset (Fin 2)).val.map (0 : Fin 2 → ℝ)
      = (Finset.univ : Finset (Fin 2)).val.map hT.eigenvalues := by rw [hε]
  have hk : (1 : ℕ) ≤ 2 := by decide
  obtain ⟨S, hScard, hSsum⟩ :=
    LatticeSystem.Math.exists_lowestLevels_finset_of_map_eq hk hmono hspec
  refine ⟨S, hScard, ?_⟩
  have hSsumR : (∑ p ∈ S, hT.eigenvalues p) = 0 := by rw [hSsum]; simp
  unfold occupiedEigenEnergy
  rw [← Complex.ofReal_sum, hSsumR, Finset.sum_empty, Complex.ofReal_zero, add_zero]

end LatticeSystem.Tests.HubbardImpossibilityLowDensity
