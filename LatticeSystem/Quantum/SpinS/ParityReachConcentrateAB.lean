import LatticeSystem.Quantum.SpinS.ParityReachConcentrateB

/-!
# Combined A+B concentration to a two-site canonical form

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Composing the A-side concentration (#3804) with the B-side concentration (#3805) gives a two-step
chain that reduces any `σ` (with appropriate room) to a config concentrated at exactly two sites
`(a₀, b₀)`: `σ' a₀ = total A-mass`, `σ' b₀ = total B-mass`, `σ' = 0` elsewhere.

This is the **two-site canonical form** target for the canonical-representative argument of (d)
reachability totality.  Any two `σ, σ'` with the same total magnetization can both reach the same
canonical, hence reach each other.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Combined A+B concentration**.  Given `a₀ ∈ A`, `b₀ ∉ A`, with the room conditions
- `hboundA`: A-side total fits at `a₀` (`(σ a₀).val + ∑_{aSitesExcept} (σ s).val ≤ N`),
- `hboundB`: B-side total fits at `b₀`,
- `hA_lt_N`: after A-concentration the resulting `σ' a₀ = total A-mass` satisfies `+ 1 ≤ N` (used
  as the temporary store for B-concentration),

`σ` is `ParityReachableS`-reachable to the config combining both drains. -/
theorem parityReachableS_concentrate_AB
    (A : V → Bool) {a₀ b₀ : V} (ha₀ : A a₀ = true) (hb₀ : A b₀ = false)
    {σ : V → Fin (N + 1)}
    (hboundA : (σ a₀).val + ∑ s ∈ aSitesExcept A a₀, (σ s).val ≤ N)
    (hboundB : (σ b₀).val + ∑ s ∈ bSitesExcept A b₀, (σ s).val ≤ N)
    (hkb₀ : (σ b₀).val + 1 ≤ N)
    (hA_lt_N : (σ a₀).val + ∑ s ∈ aSitesExcept A a₀, (σ s).val + 1 ≤ N) :
    ∃ σ_AB : V → Fin (N + 1),
      ParityReachableS (bipartiteCompleteGraphOf A) σ σ_AB ∧
      σ_AB a₀ =
        ⟨(σ a₀).val + ∑ s ∈ aSitesExcept A a₀, (σ s).val, by omega⟩ ∧
      σ_AB b₀ =
        ⟨(σ b₀).val + ∑ s ∈ bSitesExcept A b₀, (σ s).val, by omega⟩ ∧
      (∀ a ∈ aSitesExcept A a₀, σ_AB a = ⟨0, by omega⟩) ∧
      (∀ b ∈ bSitesExcept A b₀, σ_AB b = ⟨0, by omega⟩) := by
  -- Step 1: A-concentration via b₀.
  have hreach_A :=
    parityReachableS_concentrate_A_at_a0 A ha₀ hb₀ hboundA hkb₀
  set σ_A : V → Fin (N + 1) :=
    drainSetInto σ a₀ (aSitesExcept A a₀) hboundA
      (by intro h; exact (mem_aSitesExcept.mp h).2 rfl) with hsig_A
  -- σ_A properties
  have hsig_A_a₀ : σ_A a₀ =
      ⟨(σ a₀).val + ∑ s ∈ aSitesExcept A a₀, (σ s).val, by omega⟩ := by
    rw [hsig_A]; unfold drainSetInto; rw [if_pos rfl]
  have hsig_A_aSites : ∀ a ∈ aSitesExcept A a₀, σ_A a = ⟨0, by omega⟩ := by
    intro a ha
    have ha_ne_a₀ : a ≠ a₀ := (mem_aSitesExcept.mp ha).2
    rw [hsig_A]; unfold drainSetInto; rw [if_neg ha_ne_a₀, if_pos ha]
  have hsig_A_other : ∀ k, k ≠ a₀ → k ∉ aSitesExcept A a₀ → σ_A k = σ k := by
    intro k hka₀ hk
    rw [hsig_A]; unfold drainSetInto; rw [if_neg hka₀, if_neg hk]
  -- σ_A on B-sites: σ_A b = σ b (since B-sites are not in A, hence not in aSitesExcept A a₀).
  have hsig_A_bSite : ∀ b, A b = false → σ_A b = σ b := by
    intro b hAb
    have hb_ne_a₀ : b ≠ a₀ := by intro h; rw [h] at hAb; exact absurd (hAb.symm.trans ha₀) (by decide)
    have hb_notin : b ∉ aSitesExcept A a₀ := fun h => by
      have := (mem_aSitesExcept.mp h).1
      rw [hAb] at this; exact absurd this (by decide)
    exact hsig_A_other b hb_ne_a₀ hb_notin
  -- Step 2: B-concentration on σ_A via a₀ (post-A-concentration, σ_A a₀ = total A-mass).
  have hboundB_A : (σ_A b₀).val + ∑ s ∈ bSitesExcept A b₀, (σ_A s).val ≤ N := by
    rw [hsig_A_bSite b₀ hb₀]
    have hsum_eq : ∑ s ∈ bSitesExcept A b₀, (σ_A s).val =
        ∑ s ∈ bSitesExcept A b₀, (σ s).val := by
      refine Finset.sum_congr rfl (fun s hs => ?_)
      rw [hsig_A_bSite s (mem_bSitesExcept.mp hs).1]
    rw [hsum_eq]; exact hboundB
  have hka_A : (σ_A a₀).val + 1 ≤ N := by
    rw [hsig_A_a₀]; exact hA_lt_N
  have hreach_B :=
    parityReachableS_concentrate_B_at_b0 A hb₀ ha₀ hboundB_A hka_A
  set σ_AB : V → Fin (N + 1) :=
    drainSetInto σ_A b₀ (bSitesExcept A b₀) hboundB_A
      (by intro h; exact (mem_bSitesExcept.mp h).2 rfl) with hsig_AB
  refine ⟨σ_AB, ParityReachableS.trans hreach_A hreach_B, ?_, ?_, ?_, ?_⟩
  · -- σ_AB a₀ = σ_A a₀ (a₀ ∉ B-sites since a₀ ∈ A).
    have ha₀_ne_b₀ : a₀ ≠ b₀ := by intro h; rw [h] at ha₀; exact absurd (ha₀.symm.trans hb₀) (by decide)
    have ha₀_notin_B : a₀ ∉ bSitesExcept A b₀ := fun h => by
      have := (mem_bSitesExcept.mp h).1
      rw [ha₀] at this; exact absurd this (by decide)
    rw [hsig_AB]; unfold drainSetInto
    rw [if_neg ha₀_ne_b₀, if_neg ha₀_notin_B]
    have hsum_eq : ∑ s ∈ aSitesExcept A a₀, (σ s).val =
        ∑ s ∈ aSitesExcept A a₀, (σ s).val := rfl
    exact hsig_A_a₀
  · -- σ_AB b₀ = (σ_A b₀ + Σ bSitesExcept σ_A) = (σ b₀ + Σ σ_A b) = (σ b₀ + Σ σ b).
    rw [hsig_AB]; unfold drainSetInto; rw [if_pos rfl]
    ext
    show (σ_A b₀).val + ∑ s ∈ bSitesExcept A b₀, (σ_A s).val =
      (σ b₀).val + ∑ s ∈ bSitesExcept A b₀, (σ s).val
    rw [hsig_A_bSite b₀ hb₀]
    congr 1
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [hsig_A_bSite s (mem_bSitesExcept.mp hs).1]
  · intro a ha
    have ha_ne_a₀ : a ≠ a₀ := (mem_aSitesExcept.mp ha).2
    have hAa : A a = true := (mem_aSitesExcept.mp ha).1
    have ha_ne_b₀ : a ≠ b₀ := by intro h; rw [h] at hAa; exact absurd (hAa.symm.trans hb₀) (by decide)
    have ha_notin_B : a ∉ bSitesExcept A b₀ := fun h => by
      have := (mem_bSitesExcept.mp h).1
      rw [hAa] at this; exact absurd this (by decide)
    rw [hsig_AB]; unfold drainSetInto
    rw [if_neg ha_ne_b₀, if_neg ha_notin_B]
    exact hsig_A_aSites a ha
  · intro b hb
    have hb_ne_b₀ : b ≠ b₀ := (mem_bSitesExcept.mp hb).2
    rw [hsig_AB]; unfold drainSetInto
    rw [if_neg hb_ne_b₀, if_pos hb]

end LatticeSystem.Quantum
