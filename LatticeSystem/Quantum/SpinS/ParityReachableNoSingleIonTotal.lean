import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraphStructural
import LatticeSystem.Quantum.SpinS.MagSumStepDown
import LatticeSystem.Quantum.SpinS.ParityReachableNoSingleIon

/-!
# Bond-only parity reachability totality

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file proves the combinatorial totality needed for the general spin-`S`
`D >= 0` boundary.  The route avoids `SingleIonStepS`: cross-sector reductions
use only transverse transfer moves and bond-parity lower moves, while
same-sector connectivity uses the existing transverse-only bipartite
reachability theorem.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.unusedDecidableInType false in
/-- A direct bond-parity lower step decreases `magSumS` by exactly `2` and is
bond-only reachable. -/
theorem bondParityReachableS_step_down_direct
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    {σ : V → Fin (N + 1)}
    (hx : 1 ≤ (σ x).val) (hy : 1 ≤ (σ y).val) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧
      BondParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  have hadj : (bipartiteCompleteGraphOf A).Adj x y := by
    rw [bipartiteCompleteGraphOf_adj_iff]
    exact ⟨hxy, hAxy⟩
  refine ⟨configUpdateTwo σ x y
      ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩
      ⟨(σ y).val - 1, by have := (σ y).isLt; omega⟩, ?_, ?_⟩
  · exact parityBondStepS_pair_lower_magSumS_decrease hxy hx hy
  · exact BondParityReachableS.of_bond (parityBondStepS_pair_lower A hadj hx hy)

set_option linter.unusedDecidableInType false in
/-- If a site has at least two units and an opposite-color site is empty, a
transverse transfer followed by a bond-parity lower step decreases `magSumS` by
exactly `2` using only bond-generated parity moves. -/
theorem bondParityReachableS_step_down_transfer_then_lower
    (A : V → Bool) {x z : V} (hxz : x ≠ z) (hAxz : A x ≠ A z)
    {σ : V → Fin (N + 1)}
    (hx : 2 ≤ (σ x).val) (hz : (σ z).val = 0) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧
      BondParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  have hadj : (bipartiteCompleteGraphOf A).Adj x z := by
    rw [bipartiteCompleteGraphOf_adj_iff]
    exact ⟨hxz, hAxz⟩
  have hx_pos : 1 ≤ (σ x).val := by omega
  have hz_lt : (σ z).val + 1 ≤ N := by
    have := (σ x).isLt
    omega
  set σ_mid : V → Fin (N + 1) := configUpdateTwo σ x z
    ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩
    ⟨(σ z).val + 1, by omega⟩ with hσ_mid
  have h_mid_x : (σ_mid x).val = (σ x).val - 1 := by
    rw [hσ_mid, configUpdateTwo_at_a]
  have h_mid_z : (σ_mid z).val = 1 := by
    rw [hσ_mid, configUpdateTwo_at_b _ hxz]
    change (σ z).val + 1 = 1
    omega
  have hx_mid_pos : 1 ≤ (σ_mid x).val := by rw [h_mid_x]; omega
  have hz_mid_pos : 1 ≤ (σ_mid z).val := by rw [h_mid_z]
  have hstep1 := raiseLowerStepS_pair_shift_lower_a_raise_b A hadj hx_pos hz_lt
  have hstep2 := parityBondStepS_pair_lower A hadj hx_mid_pos hz_mid_pos
  refine ⟨_, ?_, BondParityReachableS.trans
      (BondParityReachableS.of_raiseLower hstep1)
      (BondParityReachableS.of_bond hstep2)⟩
  have h_final := parityBondStepS_pair_lower_magSumS_decrease (σ := σ_mid) hxz
    hx_mid_pos hz_mid_pos
  have h_mid : magSumS σ_mid = magSumS σ := by
    have h := magSumS_configUpdateTwo_eq σ hxz
      ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩
      ⟨(σ z).val + 1, by omega⟩
    simp at h
    change magSumS (configUpdateTwo σ x z _ _) = magSumS σ
    omega
  omega

set_option linter.unusedDecidableInType false in
/-- **Bond-only `magSumS` step-down**: if `2 <= magSumS σ`, then `σ` can be
connected by bond-only parity moves to a configuration whose `magSumS` is lower
by exactly `2`. -/
theorem bondParityReachableS_step_down
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false)
    {σ : V → Fin (N + 1)}
    (h_pos : 2 ≤ magSumS σ) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧
      BondParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  by_cases hCase1 : ∃ x : V, 2 ≤ (σ x).val
  · obtain ⟨x, hx⟩ := hCase1
    obtain ⟨z, hAzx⟩ := oppExists_of_hA_hB A hA_ne hB_ne x
    have hxz : x ≠ z := by
      intro h
      exact hAzx (by rw [h])
    by_cases hz_pos : 1 ≤ (σ z).val
    · have hx_pos : 1 ≤ (σ x).val := by omega
      exact bondParityReachableS_step_down_direct A hxz hAzx.symm hx_pos hz_pos
    · have hz_zero : (σ z).val = 0 := by omega
      exact bondParityReachableS_step_down_transfer_then_lower A hxz hAzx.symm hx hz_zero
  · have h_le1 : ∀ x, (σ x).val ≤ 1 := by
      intro x
      by_contra hge
      exact hCase1 ⟨x, by omega⟩
    by_cases hex_A : ∃ a : V, A a = true ∧ (σ a).val = 1
    · by_cases hex_B : ∃ b : V, A b = false ∧ (σ b).val = 1
      · obtain ⟨a, hAa, hka⟩ := hex_A
        obtain ⟨b, hAb, hkb⟩ := hex_B
        have hab : a ≠ b := by
          intro h
          rw [h] at hAa
          exact absurd (hAa.symm.trans hAb) (by decide)
        have hAab : A a ≠ A b := by rw [hAa, hAb]; decide
        exact bondParityReachableS_step_down_direct A hab hAab (by omega) (by omega)
      · have h_no_B : ∀ b, A b = false → (σ b).val = 0 := by
          intro b hAb
          have h := h_le1 b
          have hne : ¬(A b = false ∧ (σ b).val = 1) := fun h2 => hex_B ⟨b, h2⟩
          by_contra hne0
          exact hne ⟨hAb, by omega⟩
        have hAcard :
            2 ≤ (Finset.univ.filter (fun a : V => A a = true ∧ (σ a).val = 1)).card := by
          rw [← magSumS_eq_card_A_one_of_no_B A h_le1 h_no_B]
          exact h_pos
        obtain ⟨a₁, a₂, ha₁_mem, ha₂_mem, ha_ne⟩ :=
          Finset.one_lt_card_iff.mp
            (show 1 < (Finset.univ.filter
                (fun a : V => A a = true ∧ (σ a).val = 1)).card from
              Nat.lt_of_succ_le hAcard)
        obtain ⟨b, hAb⟩ := hB_ne
        have hA_a₁ : A a₁ = true := (Finset.mem_filter.mp ha₁_mem).2.1
        have hka_a₁ : (σ a₁).val = 1 := (Finset.mem_filter.mp ha₁_mem).2.2
        have hA_a₂ : A a₂ = true := (Finset.mem_filter.mp ha₂_mem).2.1
        have hka_a₂ : (σ a₂).val = 1 := (Finset.mem_filter.mp ha₂_mem).2.2
        have hkb : (σ b).val = 0 := h_no_B b hAb
        have ha₁_ne_b : a₁ ≠ b := by
          intro h
          rw [h] at hA_a₁
          exact absurd (hA_a₁.symm.trans hAb) (by decide)
        have ha₂_ne_b : a₂ ≠ b := by
          intro h
          rw [h] at hA_a₂
          exact absurd (hA_a₂.symm.trans hAb) (by decide)
        have hadj_a₁b : (bipartiteCompleteGraphOf A).Adj a₁ b := by
          rw [bipartiteCompleteGraphOf_adj_iff]
          exact ⟨ha₁_ne_b, by rw [hA_a₁, hAb]; decide⟩
        set σ_mid : V → Fin (N + 1) := configUpdateTwo σ a₁ b
          ⟨(σ a₁).val - 1, by have := (σ a₁).isLt; omega⟩
          ⟨(σ b).val + 1, by have := (σ a₁).isLt; omega⟩ with hσ_mid
        have h_mid_a₂_val : (σ_mid a₂).val = 1 := by
          rw [hσ_mid]
          rw [configUpdateTwo_agree _ _ _ _ _ _ ha_ne.symm ha₂_ne_b]
          exact hka_a₂
        have h_mid_b_val : (σ_mid b).val = 1 := by
          rw [hσ_mid, configUpdateTwo_at_b _ ha₁_ne_b]
          change (σ b).val + 1 = 1
          omega
        have hstep1 := raiseLowerStepS_pair_shift_lower_a_raise_b A hadj_a₁b
          (by omega : 1 ≤ (σ a₁).val) (by rw [hkb]; omega)
        have hstep2 := parityBondStepS_pair_lower A
          (by
            rw [bipartiteCompleteGraphOf_adj_iff]
            exact ⟨ha₂_ne_b, by rw [hA_a₂, hAb]; decide⟩)
          (by rw [h_mid_a₂_val]) (by rw [h_mid_b_val])
        refine ⟨_, ?_, BondParityReachableS.trans
          (BondParityReachableS.of_raiseLower hstep1)
          (BondParityReachableS.of_bond hstep2)⟩
        have hx_mid_pos : 1 ≤ (σ_mid a₂).val := by rw [h_mid_a₂_val]
        have hb_mid_pos : 1 ≤ (σ_mid b).val := by rw [h_mid_b_val]
        have h_final := parityBondStepS_pair_lower_magSumS_decrease (σ := σ_mid)
          ha₂_ne_b hx_mid_pos hb_mid_pos
        have h_mid : magSumS σ_mid = magSumS σ := by
          have h := magSumS_configUpdateTwo_eq σ ha₁_ne_b
            ⟨(σ a₁).val - 1, by have := (σ a₁).isLt; omega⟩
            ⟨(σ b).val + 1, by have := (σ a₁).isLt; omega⟩
          simp at h
          change magSumS (configUpdateTwo σ a₁ b _ _) = magSumS σ
          omega
        omega
    · have h_no_A : ∀ a, A a = true → (σ a).val = 0 := by
        intro a hAa
        have h := h_le1 a
        have hne : ¬(A a = true ∧ (σ a).val = 1) := fun h2 => hex_A ⟨a, h2⟩
        by_contra hne0
        exact hne ⟨hAa, by omega⟩
      by_cases hex_B : ∃ b : V, A b = false ∧ (σ b).val = 1
      · have hBcard :
            2 ≤ (Finset.univ.filter (fun b : V => A b = false ∧ (σ b).val = 1)).card := by
          rw [← magSumS_eq_card_B_one_of_no_A A h_le1 h_no_A]
          exact h_pos
        obtain ⟨b₁, b₂, hb₁_mem, hb₂_mem, hb_ne⟩ :=
          Finset.one_lt_card_iff.mp
            (show 1 < (Finset.univ.filter
                (fun b : V => A b = false ∧ (σ b).val = 1)).card from
              Nat.lt_of_succ_le hBcard)
        obtain ⟨a, hAa⟩ := hA_ne
        have hB_b₁ : A b₁ = false := (Finset.mem_filter.mp hb₁_mem).2.1
        have hkb_b₁ : (σ b₁).val = 1 := (Finset.mem_filter.mp hb₁_mem).2.2
        have hB_b₂ : A b₂ = false := (Finset.mem_filter.mp hb₂_mem).2.1
        have hkb_b₂ : (σ b₂).val = 1 := (Finset.mem_filter.mp hb₂_mem).2.2
        have hka : (σ a).val = 0 := h_no_A a hAa
        have hb₁_ne_a : b₁ ≠ a := by
          intro h
          rw [h] at hB_b₁
          exact absurd (hB_b₁.symm.trans hAa) (by decide)
        have hb₂_ne_a : b₂ ≠ a := by
          intro h
          rw [h] at hB_b₂
          exact absurd (hB_b₂.symm.trans hAa) (by decide)
        have hadj_b₁a : (bipartiteCompleteGraphOf A).Adj b₁ a := by
          rw [bipartiteCompleteGraphOf_adj_iff]
          exact ⟨hb₁_ne_a, by rw [hB_b₁, hAa]; decide⟩
        set σ_mid : V → Fin (N + 1) := configUpdateTwo σ b₁ a
          ⟨(σ b₁).val - 1, by have := (σ b₁).isLt; omega⟩
          ⟨(σ a).val + 1, by have := (σ b₁).isLt; omega⟩ with hσ_mid
        have h_mid_b₂_val : (σ_mid b₂).val = 1 := by
          rw [hσ_mid]
          rw [configUpdateTwo_agree _ _ _ _ _ _ hb_ne.symm hb₂_ne_a]
          exact hkb_b₂
        have h_mid_a_val : (σ_mid a).val = 1 := by
          rw [hσ_mid, configUpdateTwo_at_b _ hb₁_ne_a]
          change (σ a).val + 1 = 1
          omega
        have hstep1 := raiseLowerStepS_pair_shift_lower_a_raise_b A hadj_b₁a
          (by omega : 1 ≤ (σ b₁).val) (by rw [hka]; omega)
        have hstep2 := parityBondStepS_pair_lower A
          (by
            rw [bipartiteCompleteGraphOf_adj_iff]
            exact ⟨hb₂_ne_a, by rw [hB_b₂, hAa]; decide⟩)
          (by rw [h_mid_b₂_val]) (by rw [h_mid_a_val])
        refine ⟨_, ?_, BondParityReachableS.trans
          (BondParityReachableS.of_raiseLower hstep1)
          (BondParityReachableS.of_bond hstep2)⟩
        have hb_mid_pos : 1 ≤ (σ_mid b₂).val := by rw [h_mid_b₂_val]
        have ha_mid_pos : 1 ≤ (σ_mid a).val := by rw [h_mid_a_val]
        have h_final := parityBondStepS_pair_lower_magSumS_decrease (σ := σ_mid)
          hb₂_ne_a hb_mid_pos ha_mid_pos
        have h_mid : magSumS σ_mid = magSumS σ := by
          have h := magSumS_configUpdateTwo_eq σ hb₁_ne_a
            ⟨(σ b₁).val - 1, by have := (σ b₁).isLt; omega⟩
            ⟨(σ a).val + 1, by have := (σ b₁).isLt; omega⟩
          simp at h
          change magSumS (configUpdateTwo σ b₁ a _ _) = magSumS σ
          omega
        omega
      · have h_zero : magSumS σ = 0 := by
          rw [magSumS_eq_card_one_sites_of_le_one h_le1]
          have h_no_one : ∀ x : V, (σ x).val ≠ 1 := by
            intro x hx
            rcases hAx : A x with _ | _
            · exact hex_B ⟨x, hAx, hx⟩
            · exact hex_A ⟨x, hAx, hx⟩
          have hfilter_empty :
              (Finset.univ.filter (fun x : V => (σ x).val = 1)).card = 0 := by
            rw [Finset.card_eq_zero]
            ext x
            simp [h_no_one x]
          exact hfilter_empty
        omega

set_option linter.unusedDecidableInType false in
/-- Iterate bond-only step-down until `magSumS < 2`. -/
theorem bondParityReachableS_to_min_magSum_aux
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false) :
    ∀ (n : ℕ) (σ : V → Fin (N + 1)), magSumS σ = n →
      ∃ σ_min : V → Fin (N + 1),
        magSumS σ_min < 2 ∧
        BondParityReachableS (bipartiteCompleteGraphOf A) σ σ_min := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hmag
    by_cases hsmall : n < 2
    · refine ⟨σ, ?_, BondParityReachableS.refl _ _⟩
      omega
    · have h_pos : 2 ≤ magSumS σ := by omega
      obtain ⟨σ', h_mag', h_reach⟩ := bondParityReachableS_step_down A hA_ne hB_ne h_pos
      obtain ⟨σ_min, h_min_small, h_min_reach⟩ :=
        ih (magSumS σ') (by omega) σ' rfl
      exact ⟨σ_min, h_min_small, BondParityReachableS.trans h_reach h_min_reach⟩

set_option linter.unusedDecidableInType false in
/-- Every configuration reaches a `magSumS < 2` representative by bond-only
parity moves. -/
theorem bondParityReachableS_to_min_magSum
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false)
    (σ : V → Fin (N + 1)) :
    ∃ σ_min : V → Fin (N + 1),
      magSumS σ_min < 2 ∧
      BondParityReachableS (bipartiteCompleteGraphOf A) σ σ_min :=
  bondParityReachableS_to_min_magSum_aux A hA_ne hB_ne (magSumS σ) σ rfl

set_option linter.unusedDecidableInType false in
/-- **Bond-only parity reachability totality on the bipartite complete graph**:
any two configurations of the same total-magnetization parity are connected by
bond-only parity moves. -/
theorem bondParityReachableS_total
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    {σ σ' : V → Fin (N + 1)}
    (h_par : magSumS σ % 2 = magSumS σ' % 2) :
    BondParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  obtain ⟨σ_min, h_min_lt, h_reach_min⟩ :=
    bondParityReachableS_to_min_magSum A hA_ne hB_ne σ
  obtain ⟨σ'_min, h'_min_lt, h'_reach_min⟩ :=
    bondParityReachableS_to_min_magSum A hA_ne hB_ne σ'
  have h_par_min : magSumS σ_min = magSumS σ'_min := by
    have h1 := parityReachableS_magSumS_parity_eq
      (BondParityReachableS.to_parityReachableS h_reach_min)
    have h2 := parityReachableS_magSumS_parity_eq
      (BondParityReachableS.to_parityReachableS h'_reach_min)
    omega
  have h_within :=
    raiseLowerReachableS_bipartiteCompleteGraph_of_eq_magSumS A hA_ne hB_ne hN h_par_min
  have h_within_bond :
      BondParityReachableS (bipartiteCompleteGraphOf A) σ_min σ'_min :=
    BondParityReachableS.of_raiseLowerReachable h_within
  have h_back := BondParityReachableS.symm h'_reach_min
  exact (h_reach_min.trans h_within_bond).trans h_back

end LatticeSystem.Quantum
