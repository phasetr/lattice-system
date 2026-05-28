import LatticeSystem.Quantum.SpinS.ParityReachWitness

/-!
# Iterated bond-parity raise / lower moves at a single bipartite edge

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Composing the single-step bond-parity moves `parityBondStepS_pair_raise` / `_lower` (#3798) `n`
times at a fixed bipartite edge `(a, b)` shifts *both* endpoint values by `+n` (raise) or `−n`
(lower), preserving every other site.

Both endpoints flip parity at every step; iterating `n` times shifts both site values by `±n` (an
arbitrary integer, not restricted to even values).  Together with the cross-sublattice transverse
iterate (#3801) and the single-ion `±2k` iterates (#3809 / #3811 and #3812), this gives the (d.2)
machinery enough flexibility to bridge any two canonical configurations sharing the same
total-magnetization parity (see plan in `.self-local/tex/3739-theorem-2-4-design.tex`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **Iterated `n`-unit bond-parity raise**: from `σ` with `σ a + n ≤ N` and `σ b + n ≤ N`,
applying the bond-parity raise step at `(a, b)` `n` times shifts both endpoints by `+n`.

Proven by induction on `n` composing single bond-parity raise steps (#3798). -/
theorem parityReachableS_parityBond_raise_n_units
    (A : V → Bool) {a b : V}
    (hadj : (bipartiteCompleteGraphOf A).Adj a b)
    {σ : V → Fin (N + 1)} (n : ℕ)
    (hka : (σ a).val + n ≤ N) (hkb : (σ b).val + n ≤ N) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a b ⟨(σ a).val + n, by omega⟩
        ⟨(σ b).val + n, by omega⟩) := by
  induction n generalizing σ with
  | zero =>
    have hself : configUpdateTwo σ a b ⟨(σ a).val + 0, by omega⟩
        ⟨(σ b).val + 0, by omega⟩ = σ := by
      funext j
      unfold configUpdateTwo
      by_cases hja : j = a
      · rw [hja, if_pos rfl]
        ext
        change (σ a).val + 0 = (σ a).val
        omega
      · rw [if_neg hja]
        by_cases hjb : j = b
        · rw [hjb, if_pos rfl]
          ext
          change (σ b).val + 0 = (σ b).val
          omega
        · rw [if_neg hjb]
    rw [hself]
    exact ParityReachableS.refl _ _
  | succ k ih =>
    have hka_one : (σ a).val + 1 ≤ N := by omega
    have hkb_one : (σ b).val + 1 ≤ N := by omega
    have hstep1 := parityBondStepS_pair_raise A hadj hka_one hkb_one
    set σ_one : V → Fin (N + 1) :=
      configUpdateTwo σ a b ⟨(σ a).val + 1, by omega⟩
        ⟨(σ b).val + 1, by omega⟩ with hsig_one
    have hsig_one_a_val : (σ_one a).val = (σ a).val + 1 := by
      rw [hsig_one, configUpdateTwo_at_a]
    have hsig_one_b_val : (σ_one b).val = (σ b).val + 1 := by
      rw [hsig_one, configUpdateTwo_at_b _ hadj.ne]
    have hsig_one_off : ∀ j, j ≠ a → j ≠ b → σ_one j = σ j := by
      intro j hja hjb
      rw [hsig_one]; exact configUpdateTwo_agree _ _ _ _ _ j hja hjb
    have hka_ih : (σ_one a).val + k ≤ N := by rw [hsig_one_a_val]; omega
    have hkb_ih : (σ_one b).val + k ≤ N := by rw [hsig_one_b_val]; omega
    have hreach_k := ih hka_ih hkb_ih
    have htarget_eq :
        configUpdateTwo σ_one a b
          ⟨(σ_one a).val + k, by omega⟩
          ⟨(σ_one b).val + k, by omega⟩ =
        configUpdateTwo σ a b
          ⟨(σ a).val + (k + 1), by omega⟩
          ⟨(σ b).val + (k + 1), by omega⟩ := by
      funext j
      unfold configUpdateTwo
      by_cases hja : j = a
      · rw [hja, if_pos rfl, if_pos rfl]
        ext
        change (σ_one a).val + k = (σ a).val + (k + 1)
        rw [hsig_one_a_val]
        omega
      · rw [if_neg hja, if_neg hja]
        by_cases hjb : j = b
        · rw [hjb, if_pos rfl, if_pos rfl]
          ext
          change (σ_one b).val + k = (σ b).val + (k + 1)
          rw [hsig_one_b_val]
          omega
        · rw [if_neg hjb, if_neg hjb]
          exact hsig_one_off j hja hjb
    rw [← htarget_eq]
    exact ParityReachableS.trans (ParityReachableS.of_bond hstep1) hreach_k

omit [Fintype V] in
/-- **Iterated `n`-unit bond-parity lower**: from `σ` with `n ≤ σ a` and `n ≤ σ b`, applying the
bond-parity lower step at `(a, b)` `n` times shifts both endpoints by `−n`. -/
theorem parityReachableS_parityBond_lower_n_units
    (A : V → Bool) {a b : V}
    (hadj : (bipartiteCompleteGraphOf A).Adj a b)
    {σ : V → Fin (N + 1)} (n : ℕ)
    (hka : n ≤ (σ a).val) (hkb : n ≤ (σ b).val) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a b
        ⟨(σ a).val - n, by have := (σ a).isLt; omega⟩
        ⟨(σ b).val - n, by have := (σ b).isLt; omega⟩) := by
  induction n generalizing σ with
  | zero =>
    have hself : configUpdateTwo σ a b
        ⟨(σ a).val - 0, by have := (σ a).isLt; omega⟩
        ⟨(σ b).val - 0, by have := (σ b).isLt; omega⟩ = σ := by
      funext j
      unfold configUpdateTwo
      by_cases hja : j = a
      · rw [hja, if_pos rfl]
        ext
        change (σ a).val - 0 = (σ a).val
        omega
      · rw [if_neg hja]
        by_cases hjb : j = b
        · rw [hjb, if_pos rfl]
          ext
          change (σ b).val - 0 = (σ b).val
          omega
        · rw [if_neg hjb]
    rw [hself]
    exact ParityReachableS.refl _ _
  | succ k ih =>
    have hka_one : 1 ≤ (σ a).val := by omega
    have hkb_one : 1 ≤ (σ b).val := by omega
    have hstep1 := parityBondStepS_pair_lower A hadj hka_one hkb_one
    set σ_one : V → Fin (N + 1) :=
      configUpdateTwo σ a b
        ⟨(σ a).val - 1, by have := (σ a).isLt; omega⟩
        ⟨(σ b).val - 1, by have := (σ b).isLt; omega⟩ with hsig_one
    have hsig_one_a_val : (σ_one a).val = (σ a).val - 1 := by
      rw [hsig_one, configUpdateTwo_at_a]
    have hsig_one_b_val : (σ_one b).val = (σ b).val - 1 := by
      rw [hsig_one, configUpdateTwo_at_b _ hadj.ne]
    have hsig_one_off : ∀ j, j ≠ a → j ≠ b → σ_one j = σ j := by
      intro j hja hjb
      rw [hsig_one]; exact configUpdateTwo_agree _ _ _ _ _ j hja hjb
    have hka_ih : k ≤ (σ_one a).val := by rw [hsig_one_a_val]; omega
    have hkb_ih : k ≤ (σ_one b).val := by rw [hsig_one_b_val]; omega
    have hreach_k := ih hka_ih hkb_ih
    have htarget_eq :
        configUpdateTwo σ_one a b
          ⟨(σ_one a).val - k, by have := (σ_one a).isLt; omega⟩
          ⟨(σ_one b).val - k, by have := (σ_one b).isLt; omega⟩ =
        configUpdateTwo σ a b
          ⟨(σ a).val - (k + 1), by have := (σ a).isLt; omega⟩
          ⟨(σ b).val - (k + 1), by have := (σ b).isLt; omega⟩ := by
      funext j
      unfold configUpdateTwo
      by_cases hja : j = a
      · rw [hja, if_pos rfl, if_pos rfl]
        ext
        change (σ_one a).val - k = (σ a).val - (k + 1)
        rw [hsig_one_a_val]
        omega
      · rw [if_neg hja, if_neg hja]
        by_cases hjb : j = b
        · rw [hjb, if_pos rfl, if_pos rfl]
          ext
          change (σ_one b).val - k = (σ b).val - (k + 1)
          rw [hsig_one_b_val]
          omega
        · rw [if_neg hjb, if_neg hjb]
          exact hsig_one_off j hja hjb
    rw [← htarget_eq]
    exact ParityReachableS.trans (ParityReachableS.of_bond hstep1) hreach_k

end LatticeSystem.Quantum
