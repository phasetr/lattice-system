import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensity
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardKineticSpinBounds
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardOnSiteInteractionSingleDown
import LatticeSystem.Fermion.JordanWigner.Hubbard.ChargesCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveCoeffAction
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedSectorGround
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import LatticeSystem.Math.MatrixAnalysis.CourantFischer

/-!
# Test coverage for Theorem 11.4 (impossibility of ferromagnetism at low densities)

`hubbard_theorem_11_4` is an axiom pending discharge whose statement strengthens Tasaki's bare
one by a hopping scale `K` with its row-sum bound `_hK` and a filling floor `_hNen₀`. These tests
pin that signature and guard the two failure modes of such added hypotheses:

- **Red 1**: an application test that consumes the axiom with every binder, including `_hK` and
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

end LatticeSystem.Tests.HubbardImpossibilityLowDensity
