import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraphStructural
import LatticeSystem.Quantum.SpinS.MagSumStepDown
import LatticeSystem.Quantum.SpinS.ParityReachableNoParityBond

/-!
# Ion-only parity reachability totality

Issue #412 -- Tasaki Section 2.5 Theorem 2.4.

This file proves the combinatorial totality needed for the general spin-`S`
`lambda = 1`, `D > 0` boundary.  The route avoids `ParityBondStepS`: cross-
sector reductions use only transverse transfer moves and single-ion lower
moves, while same-sector connectivity uses the existing transverse-only
bipartite reachability theorem.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Section 2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.unusedDecidableInType false in
/-- A direct single-ion lower step decreases `magSumS` by exactly `2` and is
ion-only reachable. -/
theorem ionParityReachableS_step_down_singleIon
    (A : V → Bool) {x : V} {σ : V → Fin (N + 1)}
    (hx : 2 ≤ (σ x).val) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧
      IonParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  refine ⟨configUpdateOne σ x ⟨(σ x).val - 2, by have := (σ x).isLt; omega⟩, ?_, ?_⟩
  · exact singleIonStepS_lower_magSumS_decrease x hx
  · exact IonParityReachableS.of_singleIon (singleIonStepS_lower x hx)

set_option linter.unusedDecidableInType false in
/-- If two opposite-color sites both carry one unit, a transverse transfer stacks
them into a value-`2` site and a single-ion lower move decreases `magSumS` by
exactly `2`. -/
theorem ionParityReachableS_step_down_opposite_pair
    (A : V → Bool) (hN : 2 ≤ N)
    {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    {σ : V → Fin (N + 1)}
    (hx : (σ x).val = 1) (hy : (σ y).val = 1) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧
      IonParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  have hadj : (bipartiteCompleteGraphOf A).Adj x y := by
    rw [bipartiteCompleteGraphOf_adj_iff]
    exact ⟨hxy, hAxy⟩
  have hx_pos : 1 ≤ (σ x).val := by omega
  have hy_lt : (σ y).val + 1 ≤ N := by omega
  set σ_mid : V → Fin (N + 1) := configUpdateTwo σ x y
    ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩
    ⟨(σ y).val + 1, by omega⟩ with hσ_mid
  have h_mid_y : (σ_mid y).val = 2 := by
    rw [hσ_mid, configUpdateTwo_at_b _ hxy]
    change (σ y).val + 1 = 2
    omega
  have hstep1 := raiseLowerStepS_pair_shift_lower_a_raise_b A hadj hx_pos hy_lt
  have hstep2 := singleIonStepS_lower (σ := σ_mid) y (by rw [h_mid_y])
  refine ⟨configUpdateOne σ_mid y
      ⟨(σ_mid y).val - 2, by have := (σ_mid y).isLt; omega⟩, ?_,
      IonParityReachableS.trans
        (IonParityReachableS.of_raiseLower hstep1)
        (IonParityReachableS.of_singleIon hstep2)⟩
  have h_final := singleIonStepS_lower_magSumS_decrease (σ := σ_mid) y (by rw [h_mid_y])
  have h_mid : magSumS σ_mid = magSumS σ := by
    have h := magSumS_configUpdateTwo_eq σ hxy
      ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩
      ⟨(σ y).val + 1, by omega⟩
    simp at h
    change magSumS (configUpdateTwo σ x y _ _) = magSumS σ
    omega
  omega

set_option linter.unusedDecidableInType false in
/-- If two same-color sites both carry one unit, use an opposite-color temporary
site and transverse transfers to stack two units before a single-ion lower move. -/
theorem ionParityReachableS_step_down_same_color_pair
    (A : V → Bool) (hN : 2 ≤ N)
    {x y z : V} (hxy : x ≠ y) (hAxz : A x ≠ A z) (hAyz : A y ≠ A z)
    {σ : V → Fin (N + 1)}
    (hx : (σ x).val = 1) (hy : (σ y).val = 1) (hz_le : (σ z).val ≤ 1) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧
      IonParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  by_cases hz : (σ z).val = 1
  · have hxz : x ≠ z := by
      intro h
      exact hAxz (by rw [h])
    exact ionParityReachableS_step_down_opposite_pair A hN hxz hAxz hx hz
  · have hz0 : (σ z).val = 0 := by
      omega
    have hxz : x ≠ z := by
      intro h
      exact hAxz (by rw [h])
    have hyz : y ≠ z := by
      intro h
      exact hAyz (by rw [h])
    have hadj_xz : (bipartiteCompleteGraphOf A).Adj x z := by
      rw [bipartiteCompleteGraphOf_adj_iff]
      exact ⟨hxz, hAxz⟩
    have hadj_yz : (bipartiteCompleteGraphOf A).Adj y z := by
      rw [bipartiteCompleteGraphOf_adj_iff]
      exact ⟨hyz, hAyz⟩
    set σ₁ : V → Fin (N + 1) := configUpdateTwo σ x z
      ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩
      ⟨(σ z).val + 1, by omega⟩ with hσ₁
    have hσ₁_y : (σ₁ y).val = 1 := by
      rw [hσ₁]
      rw [configUpdateTwo_agree _ _ _ _ _ y hxy.symm hyz]
      exact hy
    have hσ₁_z : (σ₁ z).val = 1 := by
      rw [hσ₁, configUpdateTwo_at_b _ hxz]
      change (σ z).val + 1 = 1
      omega
    have hstep1 := raiseLowerStepS_pair_shift_lower_a_raise_b A hadj_xz
      (by omega : 1 ≤ (σ x).val) (by rw [hz0]; omega)
    set σ₂ : V → Fin (N + 1) := configUpdateTwo σ₁ y z
      ⟨(σ₁ y).val - 1, by have := (σ₁ y).isLt; omega⟩
      ⟨(σ₁ z).val + 1, by omega⟩ with hσ₂
    have hσ₂_z : (σ₂ z).val = 2 := by
      rw [hσ₂, configUpdateTwo_at_b _ hyz]
      change (σ₁ z).val + 1 = 2
      omega
    have hstep2 := raiseLowerStepS_pair_shift_lower_a_raise_b A hadj_yz
      (by rw [hσ₁_y]) (by rw [hσ₁_z]; omega)
    have hstep3 := singleIonStepS_lower (σ := σ₂) z (by rw [hσ₂_z])
    refine ⟨configUpdateOne σ₂ z
        ⟨(σ₂ z).val - 2, by have := (σ₂ z).isLt; omega⟩, ?_,
        (IonParityReachableS.of_raiseLower hstep1).trans
          ((IonParityReachableS.of_raiseLower hstep2).trans
            (IonParityReachableS.of_singleIon hstep3))⟩
    have h_final := singleIonStepS_lower_magSumS_decrease (σ := σ₂) z (by rw [hσ₂_z])
    have h_mid1 : magSumS σ₁ = magSumS σ := by
      have h := magSumS_configUpdateTwo_eq σ hxz
        ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩
        ⟨(σ z).val + 1, by omega⟩
      simp at h
      change magSumS (configUpdateTwo σ x z _ _) = magSumS σ
      omega
    have h_mid2 : magSumS σ₂ = magSumS σ₁ := by
      have h := magSumS_configUpdateTwo_eq σ₁ hyz
        ⟨(σ₁ y).val - 1, by have := (σ₁ y).isLt; omega⟩
        ⟨(σ₁ z).val + 1, by omega⟩
      simp at h
      change magSumS (configUpdateTwo σ₁ y z _ _) = magSumS σ₁
      omega
    omega

set_option linter.unusedDecidableInType false in
/-- **Ion-only `magSumS` step-down**: if `2 <= magSumS σ` and `2 <= N`, then
`σ` can be connected by transverse and single-ion moves to a configuration
whose `magSumS` is lower by exactly `2`. -/
theorem ionParityReachableS_step_down
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    {σ : V → Fin (N + 1)}
    (h_pos : 2 ≤ magSumS σ) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧
      IonParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  by_cases hCase1 : ∃ x : V, 2 ≤ (σ x).val
  · obtain ⟨x, hx⟩ := hCase1
    exact ionParityReachableS_step_down_singleIon (A := A) (x := x) (σ := σ) hx
  · have h_le1 : ∀ x, (σ x).val ≤ 1 := by
      intro x
      by_contra hge
      exact hCase1 ⟨x, by omega⟩
    have hcard :
        2 ≤ (Finset.univ.filter (fun x : V => (σ x).val = 1)).card := by
      rw [← magSumS_eq_card_one_sites_of_le_one h_le1]
      exact h_pos
    obtain ⟨x, y, hx_mem, hy_mem, hxy⟩ :=
      Finset.one_lt_card_iff.mp
        (show 1 < (Finset.univ.filter (fun x : V => (σ x).val = 1)).card from
          Nat.lt_of_succ_le hcard)
    have hx_val : (σ x).val = 1 := (Finset.mem_filter.mp hx_mem).2
    have hy_val : (σ y).val = 1 := (Finset.mem_filter.mp hy_mem).2
    by_cases hAxy_eq : A x = A y
    · obtain ⟨z, hAxz⟩ := oppExists_of_hA_hB A hA_ne hB_ne x
      have hxz_ne : A x ≠ A z := hAxz.symm
      have hAyz : A y ≠ A z := by
        intro h
        exact hxz_ne (hAxy_eq.trans h)
      exact ionParityReachableS_step_down_same_color_pair A hN hxy hxz_ne hAyz
        hx_val hy_val (h_le1 z)
    · exact ionParityReachableS_step_down_opposite_pair A hN hxy hAxy_eq hx_val hy_val

set_option linter.unusedDecidableInType false in
/-- Iterate ion-only step-down until `magSumS < 2`. -/
theorem ionParityReachableS_to_min_magSum_aux
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N) :
    ∀ (n : ℕ) (σ : V → Fin (N + 1)), magSumS σ = n →
      ∃ σ_min : V → Fin (N + 1),
        magSumS σ_min < 2 ∧
        IonParityReachableS (bipartiteCompleteGraphOf A) σ σ_min := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hmag
    by_cases hsmall : n < 2
    · refine ⟨σ, ?_, IonParityReachableS.refl _ _⟩
      omega
    · have h_pos : 2 ≤ magSumS σ := by omega
      obtain ⟨σ', h_mag', h_reach⟩ := ionParityReachableS_step_down A hA_ne hB_ne hN h_pos
      obtain ⟨σ_min, h_min_small, h_min_reach⟩ :=
        ih (magSumS σ') (by omega) σ' rfl
      exact ⟨σ_min, h_min_small, IonParityReachableS.trans h_reach h_min_reach⟩

set_option linter.unusedDecidableInType false in
/-- Every configuration reaches a `magSumS < 2` representative by ion-only
parity moves. -/
theorem ionParityReachableS_to_min_magSum
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    (σ : V → Fin (N + 1)) :
    ∃ σ_min : V → Fin (N + 1),
      magSumS σ_min < 2 ∧
      IonParityReachableS (bipartiteCompleteGraphOf A) σ σ_min :=
  ionParityReachableS_to_min_magSum_aux A hA_ne hB_ne hN (magSumS σ) σ rfl

set_option linter.unusedDecidableInType false in
/-- **Ion-only parity reachability totality on the bipartite complete graph**:
any two configurations of the same total-magnetization parity are connected by
transverse and single-ion moves when `2 <= N`. -/
theorem ionParityReachableS_total
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false)
    (hN : 2 ≤ N)
    {σ σ' : V → Fin (N + 1)}
    (h_par : magSumS σ % 2 = magSumS σ' % 2) :
    IonParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  obtain ⟨σ_min, h_min_lt, h_reach_min⟩ :=
    ionParityReachableS_to_min_magSum A hA_ne hB_ne hN σ
  obtain ⟨σ'_min, h'_min_lt, h'_reach_min⟩ :=
    ionParityReachableS_to_min_magSum A hA_ne hB_ne hN σ'
  have h_par_min : magSumS σ_min = magSumS σ'_min := by
    have h1 := parityReachableS_magSumS_parity_eq
      (IonParityReachableS.to_parityReachableS h_reach_min)
    have h2 := parityReachableS_magSumS_parity_eq
      (IonParityReachableS.to_parityReachableS h'_reach_min)
    omega
  have hN_pos : 1 ≤ N := by omega
  have h_within :=
    raiseLowerReachableS_bipartiteCompleteGraph_of_eq_magSumS A hA_ne hB_ne hN_pos h_par_min
  have h_within_ion :
      IonParityReachableS (bipartiteCompleteGraphOf A) σ_min σ'_min :=
    IonParityReachableS.of_raiseLowerReachable h_within
  have h_back := IonParityReachableS.symm h'_reach_min
  exact (h_reach_min.trans h_within_ion).trans h_back

end LatticeSystem.Quantum
