import LatticeSystem.Quantum.SpinS.ParityReachShuffle

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Iterated `n`-unit shuffles for `ParityReachableS`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Composing the single-unit shuffle (#3799) by induction on `n` gives an `n`-unit shuffle: from any
config `σ` with `n ≤ σ a`, `σ a' + n ≤ N`, and one available B-site `b` with `σ b + 1 ≤ N`, the
config obtained by shifting `n` units from `a` to `a'` is `ParityReachableS`-reachable.

This is the magnitude-iterating piece of (d) reachability totality.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **Iterated `n`-unit shuffle**: from `σ` with `n ≤ σ a`, `σ a' + n ≤ N`, `σ b + 1 ≤ N`, the
config shifting `n` units from `a` to `a'` (with `b` net unchanged) is `ParityReachableS`-reachable.

Proven by induction on `n` composing the single-unit shuffle (#3799) `n` times. -/
theorem parityReachableS_shuffle_n_units
    (A : V → Bool) {a a' b : V} (haa' : a ≠ a')
    (hab : (bipartiteCompleteGraphOf A).Adj a b)
    (ha'b : (bipartiteCompleteGraphOf A).Adj a' b)
    {σ : V → Fin (N + 1)} (n : ℕ)
    (hka : n ≤ (σ a).val) (hka' : (σ a').val + n ≤ N) (hkb : (σ b).val + 1 ≤ N) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a a' ⟨(σ a).val - n, by have := (σ a).isLt; omega⟩
        ⟨(σ a').val + n, by omega⟩) := by
  induction n generalizing σ with
  | zero =>
    have hself : configUpdateTwo σ a a' ⟨(σ a).val - 0, by have := (σ a).isLt; omega⟩
        ⟨(σ a').val + 0, by omega⟩ = σ := by
      funext j
      by_cases hja : j = a
      · rw [hja]
        unfold configUpdateTwo
        rw [if_pos rfl]
        ext; show (σ a).val - 0 = (σ a).val; omega
      · unfold configUpdateTwo
        rw [if_neg hja]
        by_cases hja' : j = a'
        · rw [hja']
          rw [if_pos rfl]
          ext; show (σ a').val + 0 = (σ a').val; omega
        · rw [if_neg hja']
    rw [hself]
    exact ParityReachableS.refl _ _
  | succ k ih =>
    -- σ → σ_one (single shuffle).
    have hka_one : 1 ≤ (σ a).val := by omega
    have hka'_one : (σ a').val + 1 ≤ N := by omega
    have hshuf1 :=
      parityReachableS_shuffle_a_to_aprime_via_b A haa' hab ha'b hka_one hka'_one hkb
    set σ_one : V → Fin (N + 1) :=
      configUpdateTwo σ a a' ⟨(σ a).val - 1, by have := (σ a).isLt; omega⟩
        ⟨(σ a').val + 1, by omega⟩ with hsig_one
    have hsig_one_a_val : (σ_one a).val = (σ a).val - 1 := by
      rw [hsig_one]; show (configUpdateTwo σ a a' _ _ a).val = _
      rw [configUpdateTwo_at_a]
    have hsig_one_a'_val : (σ_one a').val = (σ a').val + 1 := by
      rw [hsig_one]; show (configUpdateTwo σ a a' _ _ a').val = _
      rw [configUpdateTwo_at_b _ haa']
    have hsig_one_b_eq : σ_one b = σ b := by
      rw [hsig_one]; exact configUpdateTwo_agree _ _ _ _ _ b hab.ne.symm ha'b.ne.symm
    have hsig_one_off : ∀ j, j ≠ a → j ≠ a' → σ_one j = σ j := by
      intro j hja hja'
      rw [hsig_one]; exact configUpdateTwo_agree _ _ _ _ _ j hja hja'
    have hka_ih : k ≤ (σ_one a).val := by rw [hsig_one_a_val]; omega
    have hka'_ih : (σ_one a').val + k ≤ N := by rw [hsig_one_a'_val]; omega
    have hkb_ih : (σ_one b).val + 1 ≤ N := by rw [hsig_one_b_eq]; exact hkb
    have hshuf_k := ih hka_ih hka'_ih hkb_ih
    have htarget_eq :
        configUpdateTwo σ_one a a'
          ⟨(σ_one a).val - k, by have := (σ_one a).isLt; omega⟩
          ⟨(σ_one a').val + k, by omega⟩ =
        configUpdateTwo σ a a'
          ⟨(σ a).val - (k + 1), by have := (σ a).isLt; omega⟩
          ⟨(σ a').val + (k + 1), by omega⟩ := by
      funext j
      unfold configUpdateTwo
      by_cases hja : j = a
      · rw [hja, if_pos rfl, if_pos rfl]
        ext
        show (σ_one a).val - k = (σ a).val - (k + 1)
        rw [hsig_one_a_val]
        omega
      · rw [if_neg hja, if_neg hja]
        by_cases hja' : j = a'
        · rw [hja', if_pos rfl, if_pos rfl]
          ext
          show (σ_one a').val + k = (σ a').val + (k + 1)
          rw [hsig_one_a'_val]
          omega
        · rw [if_neg hja', if_neg hja']
          exact hsig_one_off j hja hja'
    rw [← htarget_eq]
    exact ParityReachableS.trans hshuf1 hshuf_k

end LatticeSystem.Quantum
