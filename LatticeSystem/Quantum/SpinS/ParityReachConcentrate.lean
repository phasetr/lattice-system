import LatticeSystem.Quantum.SpinS.ParityReachDrainOne

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Multi-site concentration via iterated drain

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Iterating `parityReachableS_drain_a_into_a0` (#3802) over a finite set `S` of sites disjoint from
the target `a₀` and the B-site `b` drains every `s ∈ S` into `a₀` in succession.  The result is
the `ParityReachableS`-reachable config with `σ' s = 0` for all `s ∈ S` and
`σ' a₀ = (σ a₀).val + ∑ s ∈ S, (σ s).val`.

This is the multi-site concentration primitive for (d) reachability totality.  Combined with the
symmetric B-side version, the canonical representative reduction follows.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The config obtained from `σ` by setting `σ s = 0` for all `s ∈ S` and accumulating those
values into `σ a₀`, leaving everything else unchanged. -/
noncomputable def drainSetInto (σ : V → Fin (N + 1)) (a₀ : V) (S : Finset V)
    (hbound : (σ a₀).val + ∑ s ∈ S, (σ s).val ≤ N) (_ha₀_notin : a₀ ∉ S) :
    V → Fin (N + 1) :=
  fun k => if k = a₀ then ⟨(σ a₀).val + ∑ s ∈ S, (σ s).val, by omega⟩
    else if k ∈ S then ⟨0, by omega⟩ else σ k

omit [Fintype V] in
/-- **Multi-site concentration via iterated drain**: `σ` is `ParityReachableS`-reachable to the
config that drains every `s ∈ S` (a finite set of A-sites disjoint from `a₀` and the B-site `b`)
into `a₀`. -/
theorem parityReachableS_drainSetInto
    (A : V → Bool) {a₀ b : V}
    (ha₀b : (bipartiteCompleteGraphOf A).Adj a₀ b)
    (S : Finset V)
    (hS_adj : ∀ s ∈ S, (bipartiteCompleteGraphOf A).Adj s b)
    (hS_ne_a₀ : ∀ s ∈ S, s ≠ a₀)
    {σ : V → Fin (N + 1)}
    (hbound : (σ a₀).val + ∑ s ∈ S, (σ s).val ≤ N) (hkb : (σ b).val + 1 ≤ N) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (drainSetInto σ a₀ S hbound (fun h => hS_ne_a₀ a₀ h rfl)) := by
  classical
  induction S using Finset.induction_on generalizing σ with
  | empty =>
    have hself : drainSetInto σ a₀ ∅ hbound (fun h => hS_ne_a₀ a₀ h rfl) = σ := by
      funext k
      unfold drainSetInto
      by_cases hka : k = a₀
      · rw [hka, if_pos rfl]
        ext
        change (σ a₀).val + ∑ s ∈ (∅ : Finset V), (σ s).val = (σ a₀).val
        simp
      · rw [if_neg hka]
        simp
    rw [hself]
    exact ParityReachableS.refl _ _
  | insert a S haS ih =>
    -- Drain `a` into `a₀` first, then apply ih to `S`.
    have ha_ne_a₀ : a ≠ a₀ := hS_ne_a₀ a (Finset.mem_insert_self a S)
    have ha_adj : (bipartiteCompleteGraphOf A).Adj a b :=
      hS_adj a (Finset.mem_insert_self a S)
    have hSum_insert : ∑ s ∈ insert a S, (σ s).val =
        (σ a).val + ∑ s ∈ S, (σ s).val := Finset.sum_insert haS
    have hroom_a : (σ a₀).val + (σ a).val ≤ N := by
      have := hbound; rw [hSum_insert] at this; omega
    -- Step 1: σ → σ_drain_a.
    have hreach1 :=
      parityReachableS_drain_a_into_a0 A ha_ne_a₀ ha_adj ha₀b hroom_a hkb
    set σ_drain_a : V → Fin (N + 1) :=
      configUpdateTwo σ a a₀ ⟨0, by omega⟩
        ⟨(σ a₀).val + (σ a).val, by omega⟩ with hsig_drain
    -- Properties of σ_drain_a.
    have hsig_drain_a : σ_drain_a a = ⟨0, by omega⟩ := by
      rw [hsig_drain]; exact configUpdateTwo_at_a _ _ _ _ _
    have hsig_drain_a₀ : σ_drain_a a₀ = ⟨(σ a₀).val + (σ a).val, by omega⟩ := by
      rw [hsig_drain]; exact configUpdateTwo_at_b _ ha_ne_a₀ _ _
    have hsig_drain_off : ∀ k, k ≠ a → k ≠ a₀ → σ_drain_a k = σ k := by
      intro k hka hka₀
      rw [hsig_drain]; exact configUpdateTwo_agree _ _ _ _ _ k hka hka₀
    -- Hypotheses for ih on S applied to σ_drain_a.
    have hS_ne_a₀_ih : ∀ s ∈ S, s ≠ a₀ :=
      fun s hs => hS_ne_a₀ s (Finset.mem_insert_of_mem hs)
    have hS_adj_ih : ∀ s ∈ S, (bipartiteCompleteGraphOf A).Adj s b :=
      fun s hs => hS_adj s (Finset.mem_insert_of_mem hs)
    -- The S-sum value is unchanged in σ_drain_a: each s ∈ S has σ_drain_a s = σ s.
    have hSum_eq : ∑ s ∈ S, (σ_drain_a s).val = ∑ s ∈ S, (σ s).val := by
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have hsa : s ≠ a := fun h => haS (h ▸ hs)
      have hsa₀ : s ≠ a₀ := hS_ne_a₀_ih s hs
      rw [hsig_drain_off s hsa hsa₀]
    have hbound_ih : (σ_drain_a a₀).val + ∑ s ∈ S, (σ_drain_a s).val ≤ N := by
      rw [hsig_drain_a₀, hSum_eq]
      change (σ a₀).val + (σ a).val + ∑ s ∈ S, (σ s).val ≤ N
      have := hbound; rw [hSum_insert] at this; omega
    have hkb_ih : (σ_drain_a b).val + 1 ≤ N := by
      rw [hsig_drain_off b ha_adj.ne.symm ha₀b.ne.symm]
      exact hkb
    have hreach2 := ih hS_adj_ih hS_ne_a₀_ih hbound_ih hkb_ih
    -- The target after the chain equals drainSetInto σ a₀ (insert a S).
    have htarget_eq :
        drainSetInto σ_drain_a a₀ S hbound_ih (fun h => hS_ne_a₀_ih a₀ h rfl) =
        drainSetInto σ a₀ (insert a S) hbound (fun h => hS_ne_a₀ a₀ h rfl) := by
      funext k
      unfold drainSetInto
      by_cases hka₀ : k = a₀
      · rw [hka₀, if_pos rfl, if_pos rfl]
        ext
        change (σ_drain_a a₀).val + ∑ s ∈ S, (σ_drain_a s).val =
          (σ a₀).val + ∑ s ∈ (insert a S), (σ s).val
        rw [hsig_drain_a₀, hSum_eq, hSum_insert]
        change (σ a₀).val + (σ a).val + ∑ s ∈ S, (σ s).val =
          (σ a₀).val + ((σ a).val + ∑ s ∈ S, (σ s).val)
        ring
      · rw [if_neg hka₀, if_neg hka₀]
        by_cases hka : k = a
        · rw [hka]
          rw [if_neg haS]  -- a ∉ S
          rw [if_pos (Finset.mem_insert_self a S)]
          rw [hsig_drain_a]
        · by_cases hkS : k ∈ S
          · rw [if_pos hkS]
            rw [if_pos (Finset.mem_insert_of_mem hkS)]
          · rw [if_neg hkS]
            have hk_notin : k ∉ insert a S := by
              rw [Finset.mem_insert]; exact fun h => h.elim hka hkS
            rw [if_neg hk_notin]
            exact hsig_drain_off k hka hka₀
    rw [← htarget_eq]
    exact ParityReachableS.trans hreach1 hreach2

end LatticeSystem.Quantum
