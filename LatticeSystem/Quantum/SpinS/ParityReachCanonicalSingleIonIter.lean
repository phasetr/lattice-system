import LatticeSystem.Quantum.SpinS.ParityReachCanonicalMagShift

/-!
# Iterated `+2k` single-ion magSum shift at the canonical bond endpoint `a₀`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Composing the canonical single-ion `+2` raise (#3808) at `a₀` by induction on `k` shifts the
canonical-site magnetization by `+2k` while keeping all other sites fixed.  This is the
magnitude-iterating piece of (d.1) reachability totality: it lets the canonical chain change
`magSumS` by `+2k` (parity preserved) using only single-ion updates at `a₀`.

This parallels the iterated transverse shuffle (#3800) and the iterated cross-sublattice transfer
(#3801).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **Iterated `+2k` single-ion raise at `a₀`**: composing the canonical `+2` raise (#3808) `k`
times.  From `σ` with `σ a₀ + 2k ≤ N`, the config obtained by setting `σ a₀ := σ a₀ + 2k` (with
all other sites unchanged) is `ParityReachableS`-reachable.

Proven by induction on `k` chaining `parityReachableS_canonical_singleIonRaise_a` (#3808). -/
theorem parityReachableS_canonical_singleIon_raise_iter_a
    (G : SimpleGraph V) {a₀ : V} {σ : V → Fin (N + 1)} (k : ℕ)
    (hka : (σ a₀).val + 2 * k ≤ N) :
    ParityReachableS G σ
      (configUpdateOne σ a₀ ⟨(σ a₀).val + 2 * k, by omega⟩) := by
  induction k generalizing σ with
  | zero =>
    have hself : configUpdateOne σ a₀ ⟨(σ a₀).val + 2 * 0, by omega⟩ = σ := by
      funext j
      unfold configUpdateOne
      by_cases hja : j = a₀
      · rw [hja, if_pos rfl]
        ext
        change (σ a₀).val + 2 * 0 = (σ a₀).val
        omega
      · rw [if_neg hja]
    rw [hself]
    exact ParityReachableS.refl _ _
  | succ m ih =>
    have hka_one : (σ a₀).val + 2 ≤ N := by omega
    have hstep1 := parityReachableS_canonical_singleIonRaise_a (a₀ := a₀) G hka_one
    set σ_one : V → Fin (N + 1) := configUpdateOne σ a₀ ⟨(σ a₀).val + 2, by omega⟩
      with hsig_one
    have hsig_one_a_val : (σ_one a₀).val = (σ a₀).val + 2 := by
      rw [hsig_one, configUpdateOne_at]
    have hsig_one_off : ∀ j, j ≠ a₀ → σ_one j = σ j := by
      intro j hja
      rw [hsig_one]; exact configUpdateOne_agree _ _ _ j hja
    have hka_ih : (σ_one a₀).val + 2 * m ≤ N := by rw [hsig_one_a_val]; omega
    have hreach_m := ih hka_ih
    have htarget_eq :
        configUpdateOne σ_one a₀ ⟨(σ_one a₀).val + 2 * m, by omega⟩ =
        configUpdateOne σ a₀ ⟨(σ a₀).val + 2 * (m + 1), by omega⟩ := by
      funext j
      unfold configUpdateOne
      by_cases hja : j = a₀
      · rw [hja, if_pos rfl, if_pos rfl]
        ext
        change (σ_one a₀).val + 2 * m = (σ a₀).val + 2 * (m + 1)
        rw [hsig_one_a_val]
        omega
      · rw [if_neg hja, if_neg hja]
        exact hsig_one_off j hja
    rw [← htarget_eq]
    exact ParityReachableS.trans hstep1 hreach_m

end LatticeSystem.Quantum
