import LatticeSystem.Quantum.SpinS.ParityReachToMinMagSum
import LatticeSystem.Quantum.SpinS.ParityReachableWithinSector
import LatticeSystem.Quantum.SpinS.ParityReachableSymm
import LatticeSystem.Quantum.SpinS.ParityReachableMagSum

/-!
# Full `ParityReachableS` totality on the bipartite complete graph

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

`parityReachableS_total_legacy`: for any two configurations sharing the same total-magnetization parity
(`magSumS σ ≡ magSumS σ' (mod 2)`), `ParityReachableS` connects them.

This closes the (d.3) reachability totality plan by chaining:
1. `parityReachableS_to_min_magSum` (#3822) on each side to reach sector-min canonical
   (`magSumS < 2`).
2. Parity preservation (`parityReachableS_magSumS_parity_eq`, #3786) forces the two sector-min
   canonicals to have equal `magSumS` (∈ {0, 1} as dictated by the shared parity).
3. Within-sector reachability lift (`parityReachableS_bipartiteCompleteGraph_of_eq_magSumS`,
   #3817) connects the two same-`magSumS` canonicals.
4. `ParityReachableS` symmetry (#3816) reverses the second side's chain.
5. Compose via `ParityReachableS.trans`.

This is exactly the totality hypothesis needed by the parity-block matrix irreducibility theorem
`shiftedDressedAxisSwappedReMatrixOnParityBlock_isIrreducible_of_parityReachable_total` (#3797),
discharging (e) PR5 of Tasaki §2.5 Theorem 2.4 obligation (1).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.unusedDecidableInType false in
/-- **`ParityReachableS` totality on the bipartite complete graph**: any two configurations of
the same total-magnetization parity are `ParityReachableS`-connected.  Discharges the
`hreach_total` hypothesis of the parity-block matrix irreducibility theorem #3797. -/
@[deprecated "Use canonical (h_intermediate-free) variant" (since := "2026-05-30")]

theorem parityReachableS_total_legacy
    (A : V → Bool)
    (hA_ne : ∃ a, A a = true)
    (hB_ne : ∃ b, A b = false)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {σ σ' : V → Fin (N + 1)}
    (h_par : magSumS σ % 2 = magSumS σ' % 2) :
    ParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  obtain ⟨σ_min, h_min_lt, h_reach_min⟩ :=
    parityReachableS_to_min_magSum A hA_ne hB_ne σ
  obtain ⟨σ'_min, h'_min_lt, h'_reach_min⟩ :=
    parityReachableS_to_min_magSum A hA_ne hB_ne σ'
  -- Parity preservation forces magSumS σ_min = magSumS σ'_min (both < 2 and same parity).
  have h_par_min : magSumS σ_min = magSumS σ'_min := by
    have h1 := parityReachableS_magSumS_parity_eq h_reach_min
    have h2 := parityReachableS_magSumS_parity_eq h'_reach_min
    omega
  -- Within-sector reachability connects the two canonicals.
  have h_within := parityReachableS_bipartiteCompleteGraph_of_eq_magSumS
    A h_intermediate h_par_min
  -- Reverse the second side via symmetry.
  have h_back := parityReachableS_symm h'_reach_min
  -- Chain σ → σ_min → σ'_min → σ'.
  exact (h_reach_min.trans h_within).trans h_back

end LatticeSystem.Quantum
