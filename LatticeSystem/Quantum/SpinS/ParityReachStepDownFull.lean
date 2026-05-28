import LatticeSystem.Quantum.SpinS.ParityReachStepDown
import LatticeSystem.Quantum.SpinS.ParityReachStepDownHard
import LatticeSystem.Quantum.SpinS.Magnetization
import Mathlib.Data.Finset.Card

/-!
# Full `parityReachableS_step_down` dispatcher for (d) reachability totality

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Combines the easy dispatcher `parityReachableS_step_down_easy` (#3819, Cases 1+2a) with the
two-step hard reducers `parityReachableS_step_down_hard_{A,B}` (#3820, Case 2b mirror) via a
Finset cardinality argument to extract the two distinct 1-sites required by the hard case.

The result: under sublattice non-emptyness (`hA_ne`, `hB_ne`) and `2 ≤ magSumS σ`, there exists
`σ'` with `magSumS σ' + 2 = magSumS σ` and `ParityReachableS σ σ'` — the complete cross-sector
step-down primitive for the (d.3) full reachability totality plan.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [DecidableEq V] in
/-- **Magnetization count when all values are at most 1**: `magSumS σ` equals the cardinality of
the set of 1-sites. -/
theorem magSumS_eq_card_one_sites_of_le_one
    {σ : V → Fin (N + 1)}
    (h_le1 : ∀ x, (σ x).val ≤ 1) :
    magSumS σ = (Finset.univ.filter (fun x : V => (σ x).val = 1)).card := by
  unfold magSumS
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : (σ x).val = 1
  · rw [if_pos h, h]
  · have := h_le1 x
    rw [if_neg h]
    omega

omit [DecidableEq V] in
/-- **Magnetization count restricted to one sublattice** when all values are at most 1 and the
other sublattice has all zeros. -/
theorem magSumS_eq_card_A_one_of_no_B
    (A : V → Bool) {σ : V → Fin (N + 1)}
    (h_le1 : ∀ x, (σ x).val ≤ 1)
    (h_no_B : ∀ b, A b = false → (σ b).val = 0) :
    magSumS σ =
      (Finset.univ.filter (fun a : V => A a = true ∧ (σ a).val = 1)).card := by
  rw [magSumS_eq_card_one_sites_of_le_one h_le1]
  congr 1
  refine Finset.filter_congr (fun x _ => ?_)
  refine ⟨fun hx => ⟨?_, hx⟩, fun ⟨_, hx⟩ => hx⟩
  by_contra hAx
  have hAx' : A x = false := by cases A x <;> simp_all
  exact absurd (h_no_B x hAx') (by rw [hx]; decide)

omit [DecidableEq V] in
/-- **Symmetric version for the other sublattice**. -/
theorem magSumS_eq_card_B_one_of_no_A
    (A : V → Bool) {σ : V → Fin (N + 1)}
    (h_le1 : ∀ x, (σ x).val ≤ 1)
    (h_no_A : ∀ a, A a = true → (σ a).val = 0) :
    magSumS σ =
      (Finset.univ.filter (fun b : V => A b = false ∧ (σ b).val = 1)).card := by
  rw [magSumS_eq_card_one_sites_of_le_one h_le1]
  congr 1
  refine Finset.filter_congr (fun x _ => ?_)
  refine ⟨fun hx => ⟨?_, hx⟩, fun ⟨_, hx⟩ => hx⟩
  by_contra hAx
  have hAx' : A x = true := by cases hax : A x <;> simp_all
  exact absurd (h_no_A x hAx') (by rw [hx]; decide)

set_option linter.unusedDecidableInType false in
/-- **Full `parityReachableS_step_down`**: under sublattice non-emptyness and `2 ≤ magSumS σ`,
there exists `σ'` with `magSumS σ' + 2 = magSumS σ` and `ParityReachableS σ σ'`.

Dispatches:
- Case 1 (some `σ x ≥ 2`): single-ion lower (#3819 via `Or.inl`).
- Case 2a (∃ A-1 site AND ∃ B-1 site): bond-parity lower (#3819 via `Or.inr`).
- Case 2b.A (∃ A-1 site, no B-1 site): hard_A (#3820) with the second A-1 site extracted via
  `Finset.one_lt_card`.
- Case 2b.B (no A-1 site, ∃ B-1 site): hard_B (#3820) symmetrically.
- Vacuous: no A-1 AND no B-1 → `magSumS σ = 0` ⊥ `h_pos`. -/
theorem parityReachableS_step_down
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false)
    {σ : V → Fin (N + 1)}
    (h_pos : 2 ≤ magSumS σ) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧
      ParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  by_cases hCase1 : ∃ x : V, 2 ≤ (σ x).val
  · exact parityReachableS_step_down_easy A (Or.inl hCase1)
  · have h_le1 : ∀ x, (σ x).val ≤ 1 := by
      intro x
      by_contra hge
      exact hCase1 ⟨x, by omega⟩
    by_cases hex_A : ∃ a : V, A a = true ∧ (σ a).val = 1
    · by_cases hex_B : ∃ b : V, A b = false ∧ (σ b).val = 1
      · -- Case 2a
        obtain ⟨a, hAa, hka⟩ := hex_A
        obtain ⟨b, hAb, hkb⟩ := hex_B
        have hab : a ≠ b := by
          intro h; rw [h] at hAa; exact absurd (hAa.symm.trans hAb) (by decide)
        have hAab : A a ≠ A b := by rw [hAa, hAb]; decide
        have hka_pos : 1 ≤ (σ a).val := by omega
        have hkb_pos : 1 ≤ (σ b).val := by omega
        exact parityReachableS_step_down_easy A
          (Or.inr ⟨a, b, hab, hAab, hka_pos, hkb_pos⟩)
      · -- Case 2b.A: no B-1 site.
        have h_no_B : ∀ b, A b = false → (σ b).val = 0 := by
          intro b hAb
          have h := h_le1 b
          have hne : ¬(A b = false ∧ (σ b).val = 1) := fun h2 => hex_B ⟨b, h2⟩
          by_contra hne0
          exact hne ⟨hAb, by omega⟩
        -- Cardinality of A-1 sites ≥ 2.
        have hAcard :
            2 ≤ (Finset.univ.filter (fun a : V => A a = true ∧ (σ a).val = 1)).card := by
          rw [← magSumS_eq_card_A_one_of_no_B A h_le1 h_no_B]; exact h_pos
        obtain ⟨a₁, a₂, ha₁_mem, ha₂_mem, ha_ne⟩ :=
          Finset.one_lt_card_iff.mp
            (show 1 < (Finset.univ.filter
                (fun a : V => A a = true ∧ (σ a).val = 1)).card from by omega)
        have hA_a₁ : A a₁ = true := (Finset.mem_filter.mp ha₁_mem).2.1
        have hka_a₁ : (σ a₁).val = 1 := (Finset.mem_filter.mp ha₁_mem).2.2
        have hA_a₂ : A a₂ = true := (Finset.mem_filter.mp ha₂_mem).2.1
        have hka_a₂ : (σ a₂).val = 1 := (Finset.mem_filter.mp ha₂_mem).2.2
        obtain ⟨b, hAb⟩ := hB_ne
        have hkb : (σ b).val = 0 := h_no_B b hAb
        exact parityReachableS_step_down_hard_A A hA_a₁ hA_a₂ hAb ha_ne hka_a₁ hka_a₂ hkb
    · -- No A-1 site.
      have h_no_A : ∀ a, A a = true → (σ a).val = 0 := by
        intro a hAa
        have h := h_le1 a
        have hne : ¬(A a = true ∧ (σ a).val = 1) := fun h2 => hex_A ⟨a, h2⟩
        by_contra hne0
        exact hne ⟨hAa, by omega⟩
      by_cases hex_B : ∃ b : V, A b = false ∧ (σ b).val = 1
      · -- Case 2b.B: no A-1 site, ∃ B-1 site.
        have hBcard :
            2 ≤ (Finset.univ.filter (fun b : V => A b = false ∧ (σ b).val = 1)).card := by
          rw [← magSumS_eq_card_B_one_of_no_A A h_le1 h_no_A]; exact h_pos
        obtain ⟨b₁, b₂, hb₁_mem, hb₂_mem, hb_ne⟩ :=
          Finset.one_lt_card_iff.mp
            (show 1 < (Finset.univ.filter
                (fun b : V => A b = false ∧ (σ b).val = 1)).card from by omega)
        have hA_b₁ : A b₁ = false := (Finset.mem_filter.mp hb₁_mem).2.1
        have hkb_b₁ : (σ b₁).val = 1 := (Finset.mem_filter.mp hb₁_mem).2.2
        have hA_b₂ : A b₂ = false := (Finset.mem_filter.mp hb₂_mem).2.1
        have hkb_b₂ : (σ b₂).val = 1 := (Finset.mem_filter.mp hb₂_mem).2.2
        obtain ⟨a, hAa⟩ := hA_ne
        have hka : (σ a).val = 0 := h_no_A a hAa
        exact parityReachableS_step_down_hard_B A hA_b₁ hA_b₂ hAa hb_ne hkb_b₁ hkb_b₂ hka
      · -- Vacuous: no A-1 AND no B-1.  Then magSumS = 0.
        exfalso
        have h_no_one : ∀ x, (σ x).val = 0 := by
          intro x
          have h1 := h_le1 x
          by_cases hAx : A x = true
          · exact h_no_A x hAx
          · have hAx' : A x = false := Bool.eq_false_iff.mpr hAx
            have hne : ¬(A x = false ∧ (σ x).val = 1) := fun h2 => hex_B ⟨x, h2⟩
            by_contra hne0
            exact hne ⟨hAx', by omega⟩
        have : magSumS σ = 0 := by
          unfold magSumS
          exact Finset.sum_eq_zero (fun x _ => h_no_one x)
        omega

end LatticeSystem.Quantum
