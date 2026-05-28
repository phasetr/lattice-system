import LatticeSystem.Quantum.SpinS.ParityReachCanonicalAligned
import LatticeSystem.Quantum.SpinS.ParityReachBondIter
import LatticeSystem.Quantum.SpinS.ParityReachTransferIter

/-!
# Full canonical-to-canonical reachability (d.2.e) — aligned + flipped dispatch

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

This file completes the (d.2) canonical-to-canonical reachability layer for the (d) reachability
totality assembly: from any starting config `σ` and any target endpoint values `(m_A', m_B')`
satisfying the same global parity, the config that updates `σ` at `(a₀, b₀)` to `(m_A', m_B')`
is `ParityReachableS`-reachable.

Strategy:
* If `m_A' ≡ (σ a₀).val` (mod 2) and `m_B' ≡ (σ b₀).val` (mod 2) (aligned case), dispatch to
  #3814 `parityReachableS_canonical_to_canonical_aligned`.
* Otherwise (flipped case, both per-endpoint parities flipped), prepend a single elementary move
  that simultaneously flips both endpoint parities — one of four options:
    1. bond-parity raise at `(a₀, b₀)` (#3813), when `(σ a₀).val + 1 ≤ N` and `(σ b₀).val + 1 ≤ N`.
    2. bond-parity lower at `(a₀, b₀)` (#3813), when `1 ≤ (σ a₀).val` and `1 ≤ (σ b₀).val`.
    3. transverse `a → b` (#3801), when `1 ≤ (σ a₀).val` and `(σ b₀).val + 1 ≤ N`.
    4. transverse `b → a` (#3801 via `hadj.symm`), when `1 ≤ (σ b₀).val` and `(σ a₀).val + 1 ≤ N`.
At least one of these four is feasible for any `(σ a₀, σ b₀)` in `[0, N]^2` with `N ≥ 1`; this is
covered by a priority dispatcher.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **Helper: `configUpdateTwo` overwrite at the same two sites**.  Updating a config that itself
came from a prior two-site update at the same sites is the same as updating from the original. -/
theorem configUpdateTwo_configUpdateTwo
    (σ : V → Fin (N + 1)) {a b : V} (hab : a ≠ b) (va vb va' vb' : Fin (N + 1)) :
    configUpdateTwo (configUpdateTwo σ a b va vb) a b va' vb' =
      configUpdateTwo σ a b va' vb' := by
  funext j
  by_cases hja : j = a
  · subst hja
    rw [configUpdateTwo_at_a, configUpdateTwo_at_a]
  · by_cases hjb : j = b
    · subst hjb
      rw [configUpdateTwo_at_b _ hab, configUpdateTwo_at_b _ hab]
    · rw [configUpdateTwo_agree _ _ _ _ _ _ hja hjb,
          configUpdateTwo_agree _ _ _ _ _ _ hja hjb,
          configUpdateTwo_agree _ _ _ _ _ _ hja hjb]

omit [Fintype V] in
/-- **Flipped-case reduction via a single elementary move** that simultaneously flips both
per-endpoint parities, restated as: given an intermediate config `σ'` reachable from `σ` whose
`(a₀, b₀)` values now align in parity with `(m_A', m_B')` and whose off-`{a₀, b₀}` sites match
`σ`, the flipped canonical-to-canonical reachability follows by chaining the adjustment step with
the aligned dispatcher (#3814). -/
theorem parityReachableS_canonical_to_canonical_via_adjustment
    (A : V → Bool) {a₀ b₀ : V}
    (hadj : (bipartiteCompleteGraphOf A).Adj a₀ b₀)
    {σ σ' : V → Fin (N + 1)} {m_A' m_B' : ℕ}
    (hmA' : m_A' ≤ N) (hmB' : m_B' ≤ N)
    (hstep : ParityReachableS (bipartiteCompleteGraphOf A) σ σ')
    (h_off : ∀ j, j ≠ a₀ → j ≠ b₀ → σ' j = σ j)
    (h_a_aligned' : (m_A' + (σ' a₀).val) % 2 = 0)
    (h_b_aligned' : (m_B' + (σ' b₀).val) % 2 = 0) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a₀ b₀ ⟨m_A', by omega⟩ ⟨m_B', by omega⟩) := by
  have h_aligned := parityReachableS_canonical_to_canonical_aligned
    (bipartiteCompleteGraphOf A) (σ := σ') hadj.ne hmA' hmB' h_a_aligned' h_b_aligned'
  have heq :
      configUpdateTwo σ' a₀ b₀ ⟨m_A', by omega⟩ ⟨m_B', by omega⟩ =
      configUpdateTwo σ a₀ b₀ ⟨m_A', by omega⟩ ⟨m_B', by omega⟩ := by
    funext j
    by_cases hja : j = a₀
    · subst hja
      rw [configUpdateTwo_at_a, configUpdateTwo_at_a]
    · by_cases hjb : j = b₀
      · subst hjb
        rw [configUpdateTwo_at_b _ hadj.ne, configUpdateTwo_at_b _ hadj.ne]
      · rw [configUpdateTwo_agree _ _ _ _ _ _ hja hjb,
            configUpdateTwo_agree _ _ _ _ _ _ hja hjb]
        exact h_off j hja hjb
  rw [heq] at h_aligned
  exact ParityReachableS.trans hstep h_aligned

omit [Fintype V] in
/-- **Full canonical-to-canonical reachability**: starting from any `σ`, the config that updates
`σ` at `(a₀, b₀)` to `(m_A', m_B')` is `ParityReachableS`-reachable whenever the total
magnetization parity is preserved. -/
theorem parityReachableS_canonical_to_canonical
    (A : V → Bool) {a₀ b₀ : V}
    (hadj : (bipartiteCompleteGraphOf A).Adj a₀ b₀)
    {σ : V → Fin (N + 1)} {m_A' m_B' : ℕ}
    (hmA' : m_A' ≤ N) (hmB' : m_B' ≤ N)
    (h_par : ((σ a₀).val + (σ b₀).val + m_A' + m_B') % 2 = 0) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a₀ b₀ ⟨m_A', by omega⟩ ⟨m_B', by omega⟩) := by
  by_cases h_a_aligned : (m_A' + (σ a₀).val) % 2 = 0
  · -- aligned case
    have h_b_aligned : (m_B' + (σ b₀).val) % 2 = 0 := by omega
    exact parityReachableS_canonical_to_canonical_aligned
      (bipartiteCompleteGraphOf A) hadj.ne hmA' hmB' h_a_aligned h_b_aligned
  · -- flipped case: dispatch to one of 4 elementary moves
    have h_a_flip : (m_A' + (σ a₀).val) % 2 = 1 := by omega
    have h_b_flip : (m_B' + (σ b₀).val) % 2 = 1 := by omega
    by_cases h1a : (σ a₀).val + 1 ≤ N
    · by_cases h1b : (σ b₀).val + 1 ≤ N
      · -- priority 1: bond-parity raise
        refine parityReachableS_canonical_to_canonical_via_adjustment A hadj hmA' hmB'
          (σ' := configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val + 1, by omega⟩
            ⟨(σ b₀).val + 1, by omega⟩) ?_ ?_ ?_ ?_
        · exact parityReachableS_parityBond_raise_n_units A hadj 1 h1a h1b
        · intro j hja hjb
          exact configUpdateTwo_agree _ _ _ _ _ _ hja hjb
        · have : (configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val + 1, by omega⟩
              ⟨(σ b₀).val + 1, by omega⟩ a₀).val = (σ a₀).val + 1 := by
            rw [configUpdateTwo_at_a]
          omega
        · have : (configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val + 1, by omega⟩
              ⟨(σ b₀).val + 1, by omega⟩ b₀).val = (σ b₀).val + 1 := by
            rw [configUpdateTwo_at_b _ hadj.ne]
          omega
      · -- σ_b = N, σ_a < N: try priority 3 transverse a→b (needs σ_a ≥ 1 too)
        have h_b_N : (σ b₀).val = N := by have := (σ b₀).isLt; omega
        by_cases h_a_pos : 1 ≤ (σ a₀).val
        · -- priority 3: transverse a→b (σ_a - 1, σ_b + 1) — but σ_b + 1 > N, fail!
          -- Actually need transverse b→a instead (σ_b - 1, σ_a + 1).
          -- Wait we're in branch σ_b = N, σ_a < N. Use trans b→a.
          -- trans b→a: σ_b ≥ 1 ✓ (=N), σ_a + 1 ≤ N ✓.
          refine parityReachableS_canonical_to_canonical_via_adjustment A hadj hmA' hmB'
            (σ' := configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val + 1, by omega⟩
              ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩) ?_ ?_ ?_ ?_
          · have hb_pos : 1 ≤ (σ b₀).val := by omega
            have htrans := parityReachableS_transfer_n_units A hadj.symm 1 hb_pos h1a
            -- htrans : ParityReachableS G σ (configUpdateTwo σ b₀ a₀ ⟨σ_b - 1⟩ ⟨σ_a + 1⟩)
            -- Want: configUpdateTwo σ a₀ b₀ ⟨σ_a + 1⟩ ⟨σ_b - 1⟩.
            -- These are equal by funext/symmetry (a₀ ≠ b₀).
            have heq :
                configUpdateTwo σ b₀ a₀ ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩
                  ⟨(σ a₀).val + 1, by omega⟩ =
                configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val + 1, by omega⟩
                  ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩ := by
              funext j
              by_cases hja : j = a₀
              · subst hja
                rw [configUpdateTwo_at_b _ hadj.ne.symm, configUpdateTwo_at_a]
              · by_cases hjb : j = b₀
                · subst hjb
                  rw [configUpdateTwo_at_a, configUpdateTwo_at_b _ hadj.ne]
                · rw [configUpdateTwo_agree _ _ _ _ _ _ hjb hja,
                      configUpdateTwo_agree _ _ _ _ _ _ hja hjb]
            rw [heq] at htrans
            exact htrans
          · intro j hja hjb
            exact configUpdateTwo_agree _ _ _ _ _ _ hja hjb
          · have : (configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val + 1, by omega⟩
                ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩ a₀).val =
                (σ a₀).val + 1 := by
              rw [configUpdateTwo_at_a]
            omega
          · have : (configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val + 1, by omega⟩
                ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩ b₀).val =
                (σ b₀).val - 1 := by
              rw [configUpdateTwo_at_b _ hadj.ne]
            omega
        · -- σ_a = 0, σ_b = N. trans b→a: σ_b ≥ 1 ✓, σ_a + 1 ≤ N ✓.
          have h_a_zero : (σ a₀).val = 0 := by omega
          have hb_pos : 1 ≤ (σ b₀).val := by omega
          refine parityReachableS_canonical_to_canonical_via_adjustment A hadj hmA' hmB'
            (σ' := configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val + 1, by omega⟩
              ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩) ?_ ?_ ?_ ?_
          · have htrans := parityReachableS_transfer_n_units A hadj.symm 1 hb_pos h1a
            have heq :
                configUpdateTwo σ b₀ a₀ ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩
                  ⟨(σ a₀).val + 1, by omega⟩ =
                configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val + 1, by omega⟩
                  ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩ := by
              funext j
              by_cases hja : j = a₀
              · subst hja
                rw [configUpdateTwo_at_b _ hadj.ne.symm, configUpdateTwo_at_a]
              · by_cases hjb : j = b₀
                · subst hjb
                  rw [configUpdateTwo_at_a, configUpdateTwo_at_b _ hadj.ne]
                · rw [configUpdateTwo_agree _ _ _ _ _ _ hjb hja,
                      configUpdateTwo_agree _ _ _ _ _ _ hja hjb]
            rw [heq] at htrans
            exact htrans
          · intro j hja hjb
            exact configUpdateTwo_agree _ _ _ _ _ _ hja hjb
          · have : (configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val + 1, by omega⟩
                ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩ a₀).val =
                (σ a₀).val + 1 := by
              rw [configUpdateTwo_at_a]
            omega
          · have : (configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val + 1, by omega⟩
                ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩ b₀).val =
                (σ b₀).val - 1 := by
              rw [configUpdateTwo_at_b _ hadj.ne]
            omega
    · -- σ_a = N. Then bond-parity raise fails. Try bond-parity lower or transverse a→b.
      have h_a_N : (σ a₀).val = N := by have := (σ a₀).isLt; omega
      have h_a_pos : 1 ≤ (σ a₀).val := by omega
      by_cases h_b_pos : 1 ≤ (σ b₀).val
      · -- priority 2: bond-parity lower
        refine parityReachableS_canonical_to_canonical_via_adjustment A hadj hmA' hmB'
          (σ' := configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val - 1, by have := (σ a₀).isLt; omega⟩
            ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩) ?_ ?_ ?_ ?_
        · exact parityReachableS_parityBond_lower_n_units A hadj 1 h_a_pos h_b_pos
        · intro j hja hjb
          exact configUpdateTwo_agree _ _ _ _ _ _ hja hjb
        · have : (configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val - 1, by have := (σ a₀).isLt; omega⟩
              ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩ a₀).val =
              (σ a₀).val - 1 := by
            rw [configUpdateTwo_at_a]
          omega
        · have : (configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val - 1, by have := (σ a₀).isLt; omega⟩
              ⟨(σ b₀).val - 1, by have := (σ b₀).isLt; omega⟩ b₀).val =
              (σ b₀).val - 1 := by
            rw [configUpdateTwo_at_b _ hadj.ne]
          omega
      · -- σ_b = 0, σ_a = N. priority 3: transverse a→b (σ_a ≥ 1 ✓, σ_b + 1 ≤ N ✓).
        have h_b_zero : (σ b₀).val = 0 := by omega
        have h_b_lt : (σ b₀).val + 1 ≤ N := by omega
        refine parityReachableS_canonical_to_canonical_via_adjustment A hadj hmA' hmB'
          (σ' := configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val - 1, by have := (σ a₀).isLt; omega⟩
            ⟨(σ b₀).val + 1, by omega⟩) ?_ ?_ ?_ ?_
        · exact parityReachableS_transfer_n_units A hadj 1 h_a_pos h_b_lt
        · intro j hja hjb
          exact configUpdateTwo_agree _ _ _ _ _ _ hja hjb
        · have : (configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val - 1, by have := (σ a₀).isLt; omega⟩
              ⟨(σ b₀).val + 1, by omega⟩ a₀).val =
              (σ a₀).val - 1 := by
            rw [configUpdateTwo_at_a]
          omega
        · have : (configUpdateTwo σ a₀ b₀ ⟨(σ a₀).val - 1, by have := (σ a₀).isLt; omega⟩
              ⟨(σ b₀).val + 1, by omega⟩ b₀).val =
              (σ b₀).val + 1 := by
            rw [configUpdateTwo_at_b _ hadj.ne]
          omega

end LatticeSystem.Quantum
