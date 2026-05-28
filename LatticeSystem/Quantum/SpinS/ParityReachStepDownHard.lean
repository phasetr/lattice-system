import LatticeSystem.Quantum.SpinS.ParityReachable
import LatticeSystem.Quantum.SpinS.ParityReachWitness
import LatticeSystem.Quantum.SpinS.MagSumStepDown
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraph

/-!
# Two-step `magSumS` reduction for the "hard" Case 2b of (d) reachability totality

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

When the easy single-step dispatcher `parityReachableS_step_down_easy` (#3819) fails — i.e. all
sites have `σ x ≤ 1` AND no bipartite-adjacent both-at-1 pair exists, so all 1-sites lie in a
single sublattice — `magSumS` can still be reduced by `2` in two elementary moves:

1. One transverse move from a 1-site in the populated sublattice to a 0-site in the other
   sublattice (seeds the latter with a 1, magSumS preserved).
2. One bond-parity lower on the now-adjacent (1, 1) pair (magSumS decreases by 2).

`parityReachableS_step_down_hard_A` and its `_B` mirror take the two distinct 1-sites and the
0-site in the other sublattice as explicit inputs.  The Finset cardinality argument that produces
these witnesses from an abstract "all 1-sites in one sublattice" hypothesis is deferred to a
follow-up PR that wires them together with the easy dispatcher into the full step-down.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.unusedDecidableInType false in
/-- **Hard Case 2b.A two-step reducer**: given two distinct A-sites both at `σ = 1` and a B-site
at `σ = 0`, perform (transverse `a₁ → b`) + (bond-parity lower `(a₂, b)`) to decrease `magSumS`
by `2` via `ParityReachableS`. -/
theorem parityReachableS_step_down_hard_A
    (A : V → Bool) {a₁ a₂ b : V}
    (ha₁ : A a₁ = true) (ha₂ : A a₂ = true) (hAb : A b = false)
    (ha_ne : a₁ ≠ a₂)
    {σ : V → Fin (N + 1)}
    (hka₁ : (σ a₁).val = 1) (hka₂ : (σ a₂).val = 1) (hkb : (σ b).val = 0) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧
      ParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  have ha₁_ne_b : a₁ ≠ b := by
    intro h; rw [h] at ha₁; exact absurd (ha₁.symm.trans hAb) (by decide)
  have ha₂_ne_b : a₂ ≠ b := by
    intro h; rw [h] at ha₂; exact absurd (ha₂.symm.trans hAb) (by decide)
  have hadj_a₁b : (bipartiteCompleteGraphOf A).Adj a₁ b := by
    rw [bipartiteCompleteGraphOf_adj_iff]; exact ⟨ha₁_ne_b, by rw [ha₁, hAb]; decide⟩
  have hadj_a₂b : (bipartiteCompleteGraphOf A).Adj a₂ b := by
    rw [bipartiteCompleteGraphOf_adj_iff]; exact ⟨ha₂_ne_b, by rw [ha₂, hAb]; decide⟩
  have hN_pos : 1 ≤ N := by have := (σ a₁).isLt; omega
  have hka₁_pos : 1 ≤ (σ a₁).val := by omega
  have hkb_lt_N : (σ b).val + 1 ≤ N := by omega
  -- σ_mid := configUpdateTwo σ a₁ b ⟨σ a₁ − 1, _⟩ ⟨σ b + 1, _⟩
  set σ_mid : V → Fin (N + 1) := configUpdateTwo σ a₁ b
    ⟨(σ a₁).val - 1, by have := (σ a₁).isLt; omega⟩
    ⟨(σ b).val + 1, by omega⟩ with hσ_mid
  -- σ_mid a₂ = σ a₂ = 1.
  have h_mid_a₂_val : (σ_mid a₂).val = 1 := by
    rw [hσ_mid]
    rw [configUpdateTwo_agree _ _ _ _ _ _ ha_ne.symm ha₂_ne_b]
    exact hka₂
  -- σ_mid b = 1.
  have h_mid_b_val : (σ_mid b).val = 1 := by
    rw [hσ_mid]
    rw [configUpdateTwo_at_b _ ha₁_ne_b]
    change (σ b).val + 1 = 1
    omega
  have hka₂_mid_pos : 1 ≤ (σ_mid a₂).val := by rw [h_mid_a₂_val]
  have hkb_mid_pos : 1 ≤ (σ_mid b).val := by rw [h_mid_b_val]
  have hstep1 := raiseLowerStepS_pair_shift_lower_a_raise_b A hadj_a₁b hka₁_pos hkb_lt_N
  have hstep2 := parityBondStepS_pair_lower A hadj_a₂b hka₂_mid_pos hkb_mid_pos
  refine ⟨_, ?_, ParityReachableS.trans (ParityReachableS.of_raiseLower hstep1)
      (ParityReachableS.of_bond hstep2)⟩
  -- magSumS bond-parity lower on σ_mid decreases by 2; transverse preserves magSumS.
  have h_final := parityBondStepS_pair_lower_magSumS_decrease (σ := σ_mid) ha₂_ne_b
    hka₂_mid_pos hkb_mid_pos
  have h_mid : magSumS σ_mid = magSumS σ := by
    have h := magSumS_configUpdateTwo_eq σ ha₁_ne_b
      ⟨(σ a₁).val - 1, by have := (σ a₁).isLt; omega⟩
      ⟨(σ b).val + 1, by omega⟩
    simp at h
    change magSumS (configUpdateTwo σ a₁ b _ _) = magSumS σ
    omega
  omega

set_option linter.unusedDecidableInType false in
/-- **Hard Case 2b.B two-step reducer**: symmetric to `_hard_A` with A and B swapped. -/
theorem parityReachableS_step_down_hard_B
    (A : V → Bool) {b₁ b₂ a : V}
    (hb₁ : A b₁ = false) (hb₂ : A b₂ = false) (hAa : A a = true)
    (hb_ne : b₁ ≠ b₂)
    {σ : V → Fin (N + 1)}
    (hkb₁ : (σ b₁).val = 1) (hkb₂ : (σ b₂).val = 1) (hka : (σ a).val = 0) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧
      ParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  have hb₁_ne_a : b₁ ≠ a := by
    intro h; rw [h] at hb₁; exact absurd (hb₁.symm.trans hAa) (by decide)
  have hb₂_ne_a : b₂ ≠ a := by
    intro h; rw [h] at hb₂; exact absurd (hb₂.symm.trans hAa) (by decide)
  have hadj_b₁a : (bipartiteCompleteGraphOf A).Adj b₁ a := by
    rw [bipartiteCompleteGraphOf_adj_iff]; exact ⟨hb₁_ne_a, by rw [hb₁, hAa]; decide⟩
  have hadj_b₂a : (bipartiteCompleteGraphOf A).Adj b₂ a := by
    rw [bipartiteCompleteGraphOf_adj_iff]; exact ⟨hb₂_ne_a, by rw [hb₂, hAa]; decide⟩
  have hN_pos : 1 ≤ N := by have := (σ b₁).isLt; omega
  have hkb₁_pos : 1 ≤ (σ b₁).val := by omega
  have hka_lt_N : (σ a).val + 1 ≤ N := by omega
  set σ_mid : V → Fin (N + 1) := configUpdateTwo σ b₁ a
    ⟨(σ b₁).val - 1, by have := (σ b₁).isLt; omega⟩
    ⟨(σ a).val + 1, by omega⟩ with hσ_mid
  have h_mid_b₂_val : (σ_mid b₂).val = 1 := by
    rw [hσ_mid]
    rw [configUpdateTwo_agree _ _ _ _ _ _ hb_ne.symm hb₂_ne_a]
    exact hkb₂
  have h_mid_a_val : (σ_mid a).val = 1 := by
    rw [hσ_mid]
    rw [configUpdateTwo_at_b _ hb₁_ne_a]
    change (σ a).val + 1 = 1
    omega
  have hkb₂_mid_pos : 1 ≤ (σ_mid b₂).val := by rw [h_mid_b₂_val]
  have hka_mid_pos : 1 ≤ (σ_mid a).val := by rw [h_mid_a_val]
  have hstep1 := raiseLowerStepS_pair_shift_lower_a_raise_b A hadj_b₁a hkb₁_pos hka_lt_N
  have hstep2 := parityBondStepS_pair_lower A hadj_b₂a hkb₂_mid_pos hka_mid_pos
  refine ⟨_, ?_, ParityReachableS.trans (ParityReachableS.of_raiseLower hstep1)
      (ParityReachableS.of_bond hstep2)⟩
  have h_final := parityBondStepS_pair_lower_magSumS_decrease (σ := σ_mid) hb₂_ne_a
    hkb₂_mid_pos hka_mid_pos
  have h_mid : magSumS σ_mid = magSumS σ := by
    have h := magSumS_configUpdateTwo_eq σ hb₁_ne_a
      ⟨(σ b₁).val - 1, by have := (σ b₁).isLt; omega⟩
      ⟨(σ a).val + 1, by omega⟩
    simp at h
    change magSumS (configUpdateTwo σ b₁ a _ _) = magSumS σ
    omega
  omega

end LatticeSystem.Quantum
