import LatticeSystem.Quantum.SpinS.ParityReachable
import LatticeSystem.Quantum.SpinS.ParityReachWitness
import LatticeSystem.Quantum.SpinS.MagSumStepDown
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraph

/-!
# Single-step `magSumS` reduction (easy cases) for (d) reachability totality

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

`parityReachableS_step_down_easy` decreases `magSumS` by exactly `2` in one elementary
`ParityStepS` move, dispatched on a disjunctive hypothesis covering the two easy cases:

1. **Single-ion lower** — some site has `σ x ≥ 2` (one move at that site).
2. **Bond-parity lower** — some bipartite-adjacent pair `(a, b)` has both `σ a ≥ 1` and
   `σ b ≥ 1` (one move at that pair).

The remaining "hard" case (all `σ x ≤ 1` and no bipartite-adjacent both-at-1 pair, i.e. all
non-zero sites in a single sublattice) reduces in two elementary moves (one transverse to seed
the other sublattice, then bond-parity lower) and is handled in a follow-up PR.

Combined with the per-sector iteration and the within-sector reachability (#3817) + symmetry
(#3816), this builds toward the (d.3) full reachability totality discharging the
`hreach_total` hypothesis of the parity-block matrix irreducibility theorem (#3797).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.unusedDecidableInType false in
/-- **Single-step magSumS step-down (easy cases)**: given a disjunctive witness — either a site
with `σ x ≥ 2` (single-ion lower target) or a bipartite-adjacent pair with both `≥ 1`
(bond-parity lower target) — there exists `σ'` with `magSumS σ' + 2 = magSumS σ` and
`ParityReachableS σ σ'`. -/
theorem parityReachableS_step_down_easy
    (A : V → Bool) {σ : V → Fin (N + 1)}
    (h_dispatch :
      (∃ x : V, 2 ≤ (σ x).val) ∨
      (∃ a b : V, a ≠ b ∧ A a ≠ A b ∧ 1 ≤ (σ a).val ∧ 1 ≤ (σ b).val)) :
    ∃ σ' : V → Fin (N + 1),
      magSumS σ' + 2 = magSumS σ ∧
      ParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  rcases h_dispatch with ⟨x, hx⟩ | ⟨a, b, hab, hAab, hka, hkb⟩
  · -- Case 1: single-ion lower at x.
    refine ⟨configUpdateOne σ x ⟨(σ x).val - 2, by have := (σ x).isLt; omega⟩, ?_, ?_⟩
    · exact singleIonStepS_lower_magSumS_decrease x hx
    · exact ParityReachableS.of_singleIon (singleIonStepS_lower x hx)
  · -- Case 2a: bond-parity lower at adjacent (a, b).
    have hadj : (bipartiteCompleteGraphOf A).Adj a b := by
      rw [bipartiteCompleteGraphOf_adj_iff]
      exact ⟨hab, hAab⟩
    refine ⟨configUpdateTwo σ a b ⟨(σ a).val - 1, by have := (σ a).isLt; omega⟩
            ⟨(σ b).val - 1, by have := (σ b).isLt; omega⟩, ?_, ?_⟩
    · exact parityBondStepS_pair_lower_magSumS_decrease hab hka hkb
    · exact ParityReachableS.of_bond (parityBondStepS_pair_lower A hadj hka hkb)

end LatticeSystem.Quantum
