import LatticeSystem.Fermion.JordanWigner

/-!
# Test coverage for Theorem 11.4 (impossibility of ferromagnetism at low densities)

PR-1 of the Theorem 11.4 discharge arc (issue #5363) sharpens
`hubbard_theorem_11_4`'s statement (adding `K` and `_hK`, `_hNen₀`) without discharging the
axiom. These tests pin the sharpened signature and guard the two failure modes of the change:

- **Red 1**: an application test that consumes the axiom with every binder including the two new
  ones (`_hK`, `_hNen₀`). It fails to elaborate against the *unedited* axiom (wrong arity at `K`,
  missing arguments), and elaborates once the axiom's signature is corrected.
- **Red 2**: the sharpened filling hypotheses (`2 ≤ Ne`, `2 * n₀ ≤ Ne`, `Ne/(N+1) ≤ ρ₁`) are
  jointly satisfiable for every `ρ₁ > 0` and `n₀` — guards against under-quantification (vacuity).
- **Red 3**: every Hermitian hopping matrix admits *some* uniform row-sum bound `K` — guards that
  `_hK` restricts only the order of quantifiers, never a single model.
-/

namespace LatticeSystem.Tests.HubbardImpossibilityLowDensity

open LatticeSystem.Fermion

/-- **Red 1.** Applying `hubbard_theorem_11_4` with the sharpened signature (`K` in third
position, plus `hK` and `hNen₀`). Fails to elaborate against the current (unedited) axiom. -/
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

/-- **Red 2.** The sharpened filling hypotheses (`2 ≤ Ne`, `2 * n₀ ≤ Ne`, `Ne/(N+1) ≤ ρ₁`) are
jointly satisfiable for every `ρ₁ > 0` and `n₀`: guards against the *opposite* failure mode of
adding hypotheses (under-quantification / vacuity). -/
example (ρ₁ : ℝ) (hρ₁ : 0 < ρ₁) (n₀ : ℕ) :
    ∃ N Ne : ℕ, 2 ≤ Ne ∧ 2 * n₀ ≤ Ne ∧ (Ne : ℝ) / (N + 1) ≤ ρ₁ := by
  set Ne := max 2 (2 * n₀) with hNe_def
  obtain ⟨M, hM⟩ := exists_nat_gt ((Ne : ℝ) / ρ₁)
  refine ⟨M, Ne, le_max_left _ _, le_max_right _ _, ?_⟩
  have hM0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hM0]
  have hMNe : (Ne : ℝ) / ρ₁ < M := hM
  rw [div_lt_iff₀ hρ₁] at hMNe
  nlinarith [hMNe]

/-- **Red 3.** Every Hermitian hopping matrix admits a uniform row-sum bound `K`: `_hK` restricts
only the order of quantifiers (`ρ₁` before `∀ t`), never a single model. -/
example (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) :
    ∃ K : ℝ, ∀ x : Fin (N + 1), ∑ y : Fin (N + 1), ‖t x y‖ ≤ K := by
  exact ⟨Finset.univ.sup' Finset.univ_nonempty (fun x => ∑ y, ‖t x y‖),
    fun x => Finset.le_sup' (fun x => ∑ y, ‖t x y‖) (Finset.mem_univ x)⟩

end LatticeSystem.Tests.HubbardImpossibilityLowDensity
