import LatticeSystem.Quantum.SpinS.ParityReachWitness

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Two-step parity reachability: intra-sublattice shuffles via the other sublattice

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Foundational reachability chains used in (d) reachability totality.  Two transverse
`RaiseLowerStepS` moves at `(a, b)` and `(a', b)` (with `a, a'` on the same sublattice and `b` on
the opposite sublattice, `a ≠ a'`) compose into a *shuffle* that transfers one unit of
magnetization from `a` to `a'` (with `b` returning to its original value).  Symmetrically for the
opposite sublattice.

This is the canonical "use the opposite sublattice as a temporary store" trick for the bipartite
complete graph.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] in
/-- **A-side magnetization shuffle via B-site.**  Composing two transverse moves —
`(a, b)`-lower-a-raise-b followed by `(a', b)`-raise-a'-lower-b — transfers one unit from `a` to
`a'` (with `b` unchanged net).  Hypotheses: `a ≠ a'`, both `(a, b)` and `(a', b)` bipartite edges,
`1 ≤ σ a`, `σ a' + 1 ≤ N`, `σ b + 1 ≤ N` (so the intermediate raise of `b` is valid). -/
theorem parityReachableS_shuffle_a_to_aprime_via_b
    (A : V → Bool) {a a' b : V} (haa' : a ≠ a')
    (hab : (bipartiteCompleteGraphOf A).Adj a b)
    (ha'b : (bipartiteCompleteGraphOf A).Adj a' b)
    {σ : V → Fin (N + 1)}
    (hka : 1 ≤ (σ a).val) (hka' : (σ a').val + 1 ≤ N) (hkb : (σ b).val + 1 ≤ N) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ
      (configUpdateTwo σ a a' ⟨(σ a).val - 1, by have := (σ a).isLt; omega⟩
        ⟨(σ a').val + 1, by omega⟩) := by
  have ha'a : a' ≠ a := haa'.symm
  have hab_ne : a ≠ b := hab.ne
  have ha'b_ne : a' ≠ b := ha'b.ne
  -- Step 1: σ → σ_mid where σ_mid = σ with σ a -= 1 and σ b += 1.
  set σ_mid : V → Fin (N + 1) :=
    configUpdateTwo σ a b ⟨(σ a).val - 1, by have := (σ a).isLt; omega⟩
      ⟨(σ b).val + 1, by omega⟩ with hsig_mid
  have hstep1 : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ_mid :=
    raiseLowerStepS_pair_shift_lower_a_raise_b A hab hka hkb
  -- σ_mid values at a, a', b
  have hsig_mid_a : σ_mid a = ⟨(σ a).val - 1, by have := (σ a).isLt; omega⟩ := by
    rw [hsig_mid]; exact configUpdateTwo_at_a _ _ _ _ _
  have hsig_mid_b : σ_mid b = ⟨(σ b).val + 1, by omega⟩ := by
    rw [hsig_mid]; exact configUpdateTwo_at_b _ hab_ne _ _
  have hsig_mid_a' : σ_mid a' = σ a' := by
    rw [hsig_mid]; exact configUpdateTwo_agree _ _ _ _ _ a' ha'a ha'b_ne
  -- Step 2: σ_mid → σ_final where σ_final = σ_mid with σ_mid a' += 1, σ_mid b -= 1.
  have hka'_mid : (σ_mid a').val + 1 ≤ N := by rw [hsig_mid_a']; exact hka'
  have hkb_mid : 1 ≤ (σ_mid b).val := by rw [hsig_mid_b]; show 1 ≤ (σ b).val + 1; omega
  have hstep2 := raiseLowerStepS_pair_shift_raise_a_lower_b (N := N) A ha'b hka'_mid hkb_mid
  -- Show the final config equals our target.
  have hfinal_eq :
      configUpdateTwo σ_mid a' b ⟨(σ_mid a').val + 1, by omega⟩
        ⟨(σ_mid b).val - 1, by have := (σ_mid b).isLt; omega⟩ =
      configUpdateTwo σ a a' ⟨(σ a).val - 1, by have := (σ a).isLt; omega⟩
        ⟨(σ a').val + 1, by omega⟩ := by
    funext k
    by_cases hka_k : k = a
    · -- k = a: LHS goes through σ_mid k = σ_mid a, RHS picks the σ a - 1 entry.
      have h_ka' : k ≠ a' := hka_k ▸ haa'
      have h_kb : k ≠ b := hka_k ▸ hab_ne
      simp only [configUpdateTwo, if_neg h_ka', if_neg h_kb, if_pos hka_k]
      -- LHS = σ_mid k.  Need σ_mid k = ⟨σ a - 1, _⟩.
      rw [hka_k, hsig_mid_a]
    · by_cases hka'_k : k = a'
      · have h_ka : k ≠ a := hka'_k ▸ ha'a
        have h_kb : k ≠ b := hka'_k ▸ ha'b_ne
        simp only [configUpdateTwo, if_neg h_ka, if_pos hka'_k]
        ext
        show (σ_mid a').val + 1 = (σ a').val + 1
        rw [hsig_mid_a']
      · by_cases hkb_k : k = b
        · have h_ka : k ≠ a := hkb_k ▸ fun h => hab_ne h.symm
          have h_ka' : k ≠ a' := hkb_k ▸ fun h => ha'b_ne h.symm
          simp only [configUpdateTwo, if_neg h_ka, if_neg h_ka', if_pos hkb_k]
          ext
          show (σ_mid b).val - 1 = (σ k).val
          rw [hkb_k, hsig_mid_b]
          show (σ b).val + 1 - 1 = (σ b).val
          omega
        · simp only [configUpdateTwo, if_neg hka_k, if_neg hka'_k, if_neg hkb_k]
          rw [hsig_mid]
          simp [configUpdateTwo, hka_k, hkb_k]
  rw [← hfinal_eq]
  exact ParityReachableS.trans
    (ParityReachableS.of_raiseLower hstep1)
    (ParityReachableS.of_raiseLower hstep2)

end LatticeSystem.Quantum
