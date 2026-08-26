import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensity
import LatticeSystem.Fermion.JordanWigner.Hubbard.ChargesCore
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

PR-2 (spin-resolved kinetic layer, `.self-local/docs/theorem-11-4-pr2-design.md` §4) adds:

- **Red 4**: the primary Red (Method C, `rfl` bridge). Pins `hubbardKinetic` as the `σ`-sum of
  `hubbardKineticSpin`, and that the `σ = 1` fiber really is the spin-**down** hopping term.
  `hubbardKineticSpin` does not exist yet, so both examples fail to elaborate — this *is* the
  Red evidence.
- **Red 5**: the consumption test for the later Loewner bound `Ĥ^σ ≤ e·N̂_σ` (PR-6 (E)); pins the
  exact `rayleighOnVec` shape the bound must produce.
- **Red 6**: the consumption test for the fully-polarized kill `Ĥ↓Φ = 0` (PR-7 (H)); pins that the
  spin decomposition plus the kill collapse `hubbardKinetic` to its up-only fiber.
- **Red 7**: non-vacuity guard (mirrors Red 3) — every Hermitian matrix admits *some* uniform
  eigenvalue ceiling `e`, so the later `∀ j, ε_j ≤ e` hypothesis restricts only the order of
  quantifiers, never a single model. This one is provable today with existing API (Green).
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

/-- **Red 4a.** `hubbardKinetic` decomposes as the `σ`-sum of `hubbardKineticSpin`.
`hubbardKineticSpin` does not exist yet, so this fails to elaborate: the Red evidence for the
`rfl` bridge PR-2 must supply. -/
example (t : Fin 2 → Fin 2 → ℂ) :
    hubbardKinetic 1 t = ∑ σ : Fin 2, hubbardKineticSpin 1 t σ := rfl

/-- **Red 4b.** The `σ = 1` fiber of `hubbardKineticSpin` really is the spin-**down** hopping
term (it would break if the spin tag were flipped, which no type ever checks).
`hubbardKineticSpin` does not exist yet, so this fails to elaborate. -/
example (t : Fin 2 → Fin 2 → ℂ) :
    hubbardKineticSpin 1 t 1
      = ∑ i : Fin 2, ∑ j : Fin 2, t i j • (fermionDownCreation 1 i * fermionDownAnnihilation 1 j) :=
  rfl

/-- **Red 5.** The consumption test for the later Loewner bound `Ĥ^σ ≤ e·N̂_σ` (PR-6 (E)): pins
the exact `rayleighOnVec` shape the bound must produce. `hubbardKineticSpin` and
`hubbardKineticSpin_le_smul_sum_spinSiteNumber` do not exist yet, so this fails to elaborate. -/
example {M : ℕ} {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian) (e : ℝ)
    (he : ∀ j : Fin (M + 1), hT.eigenvalues j ≤ e) (v : (Fin (2 * M + 2) → Fin 2) → ℂ) :
    rayleighOnVec (hubbardKineticSpin M t 1) v ≤ e * rayleighOnVec (fermionTotalDownNumber M) v := by
  have hbound := rayleighOnVec_mono (hubbardKineticSpin_le_smul_sum_spinSiteNumber hT 1 he) v
  rwa [rayleighOnVec_real_smul] at hbound

/-- **Red 6.** The consumption test for the fully-polarized kill `Ĥ↓Φ = 0` (PR-7 (H)): the spin
decomposition plus the kill collapse `hubbardKinetic` to its up-only fiber. `hubbardKineticSpin`
and `hubbardKineticSpin_one_mulVec_eq_zero_of_downNumber_zero` do not exist yet, so this fails to
elaborate. -/
example (M : ℕ) (t : Fin (M + 1) → Fin (M + 1) → ℂ) (Φ : (Fin (2 * M + 2) → Fin 2) → ℂ)
    (hΦ : (fermionTotalDownNumber M).mulVec Φ = 0) :
    (hubbardKinetic M t).mulVec Φ = (hubbardKineticSpin M t 0).mulVec Φ := by
  have hadd := hubbardKinetic_eq_hubbardKineticSpin_add M t
  have hdown := hubbardKineticSpin_one_mulVec_eq_zero_of_downNumber_zero M t hΦ
  rw [hadd, Matrix.add_mulVec, hdown, add_zero]

/-- **Red 7.** Non-vacuity guard (mirrors Red 3): every Hermitian matrix admits *some* uniform
eigenvalue ceiling `e`, so `∀ j, ε_j ≤ e` restricts only the order of quantifiers, never a single
model. Provable today with existing API. -/
example {M : ℕ} {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian) :
    ∃ e : ℝ, ∀ j : Fin (M + 1), hT.eigenvalues j ≤ e :=
  ⟨Finset.univ.sup' Finset.univ_nonempty hT.eigenvalues,
    fun j => Finset.le_sup' hT.eigenvalues (Finset.mem_univ j)⟩

end LatticeSystem.Tests.HubbardImpossibilityLowDensity
