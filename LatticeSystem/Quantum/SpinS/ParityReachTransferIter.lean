import LatticeSystem.Quantum.SpinS.ParityReachWitness

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Iterated cross-sublattice transfer at a single bond

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Repeating a transverse `RaiseLowerStepS` at a single bipartite bond `(a, b)` `n` times shifts `n`
units from `a` to `b`.  The lemma `parityReachableS_transfer_n_units` packages this iteration
under the hypotheses `n ≤ σ a` and `σ b + n ≤ N`.

This is the cross-sublattice analogue of the intra-sublattice shuffle iterate (#3800), and another
foundational primitive for (d) reachability totality.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **Iterated `n`-unit cross-sublattice transfer**: from `σ` with `n ≤ σ a` and `σ b + n ≤ N`, the
config shifting `n` units from `a` to `b` is `ParityReachableS`-reachable.

Proven by induction on `n` composing single transverse moves at the same bond `(a, b)`. -/
theorem parityReachableS_transfer_n_units
    (A : V → Bool) {a b : V}
    (hab : (bipartiteCompleteGraphOf A).Adj a b)
    {σ : V → Fin (N + 1)} (n : ℕ)
    (hka : n ≤ (σ a).val) (hkb : (σ b).val + n ≤ N) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a b ⟨(σ a).val - n, by have := (σ a).isLt; omega⟩
        ⟨(σ b).val + n, by omega⟩) := by
  induction n generalizing σ with
  | zero =>
    have hself : configUpdateTwo σ a b ⟨(σ a).val - 0, by have := (σ a).isLt; omega⟩
        ⟨(σ b).val + 0, by omega⟩ = σ := by
      funext j
      by_cases hja : j = a
      · rw [hja]
        unfold configUpdateTwo
        rw [if_pos rfl]
        ext; show (σ a).val - 0 = (σ a).val; omega
      · unfold configUpdateTwo
        rw [if_neg hja]
        by_cases hjb : j = b
        · rw [hjb, if_pos rfl]
          ext; show (σ b).val + 0 = (σ b).val; omega
        · rw [if_neg hjb]
    rw [hself]
    exact ParityReachableS.refl _ _
  | succ k ih =>
    -- σ → σ_one (single transverse lower-a-raise-b).
    have hka_one : 1 ≤ (σ a).val := by omega
    have hkb_one : (σ b).val + 1 ≤ N := by omega
    have hstep1 := raiseLowerStepS_pair_shift_lower_a_raise_b A hab hka_one hkb_one
    set σ_one : V → Fin (N + 1) :=
      configUpdateTwo σ a b ⟨(σ a).val - 1, by have := (σ a).isLt; omega⟩
        ⟨(σ b).val + 1, by omega⟩ with hsig_one
    have hsig_one_a_val : (σ_one a).val = (σ a).val - 1 := by
      rw [hsig_one]; show (configUpdateTwo σ a b _ _ a).val = _
      rw [configUpdateTwo_at_a]
    have hsig_one_b_val : (σ_one b).val = (σ b).val + 1 := by
      rw [hsig_one]; show (configUpdateTwo σ a b _ _ b).val = _
      rw [configUpdateTwo_at_b _ hab.ne]
    have hsig_one_off : ∀ j, j ≠ a → j ≠ b → σ_one j = σ j := by
      intro j hja hjb
      rw [hsig_one]; exact configUpdateTwo_agree _ _ _ _ _ j hja hjb
    have hka_ih : k ≤ (σ_one a).val := by rw [hsig_one_a_val]; omega
    have hkb_ih : (σ_one b).val + k ≤ N := by rw [hsig_one_b_val]; omega
    have hreach_k := ih hka_ih hkb_ih
    have htarget_eq :
        configUpdateTwo σ_one a b
          ⟨(σ_one a).val - k, by have := (σ_one a).isLt; omega⟩
          ⟨(σ_one b).val + k, by omega⟩ =
        configUpdateTwo σ a b
          ⟨(σ a).val - (k + 1), by have := (σ a).isLt; omega⟩
          ⟨(σ b).val + (k + 1), by omega⟩ := by
      funext j
      unfold configUpdateTwo
      by_cases hja : j = a
      · rw [hja, if_pos rfl, if_pos rfl]
        ext
        show (σ_one a).val - k = (σ a).val - (k + 1)
        rw [hsig_one_a_val]
        omega
      · rw [if_neg hja, if_neg hja]
        by_cases hjb : j = b
        · rw [hjb, if_pos rfl, if_pos rfl]
          ext
          show (σ_one b).val + k = (σ b).val + (k + 1)
          rw [hsig_one_b_val]
          omega
        · rw [if_neg hjb, if_neg hjb]
          exact hsig_one_off j hja hjb
    rw [← htarget_eq]
    exact ParityReachableS.trans (ParityReachableS.of_raiseLower hstep1) hreach_k

end LatticeSystem.Quantum
