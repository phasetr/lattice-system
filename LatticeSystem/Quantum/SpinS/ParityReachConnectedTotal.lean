import LatticeSystem.Quantum.SpinS.ParityReachConnectedStepDown
import LatticeSystem.Quantum.SpinS.ParityReachableWithinSector
import LatticeSystem.Quantum.SpinS.ParityReachableSymm
import LatticeSystem.Quantum.SpinS.ParityReachableMagSum

/-!
# Connected-graph totality of parity-block reachability

Issue #5473 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

On a graph `G` with `G.Connected`, any two configurations of equal `magSumS`-parity are related
by `ParityReachableS` (under `1 ≤ N`), by `IonParityReachableS` (under `2 ≤ N`, the room the
single-ion `±2` move needs) and by `BondParityReachableS` (under `1 ≤ N` and `Nontrivial V`,
without which the one-vertex graph carries no bond move at all).  Unlike their complete-bipartite
counterparts (`parityReachableS_total`, `ionParityReachableS_total`,
`bondParityReachableS_total`), these carry **no** bipartiteness or balanced-sublattice
hypothesis: reachability along the three relations is purely graph-theoretic, and the
bipartite structure of §2.5 is needed only downstream, by the sign gauge and the sector
argument.  Mathematically the complete-bipartite trio is a special case: `hA_ne` together with
`hB_ne` already makes `bipartiteCompleteGraphOf A` connected, via
`bipartiteCompleteGraphOf_preconnected` (`BipartiteCompleteGraph.lean`) plus `Nonempty V`; only the
thin `.Connected`-packaging wrapper is absent, so neither family is stated in terms of the other
and both remain in use.

The route is the same in all three cases: descend both configurations to magnetization sum
below `2` (`ParityReachConnectedStepDown.lean`), where equal parity forces equal magnetization
sum; close the remaining gap with the magnetization-preserving connected-graph engine
`raiseLowerReachableS_of_connected`; and compose with symmetry.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, pp. 43–44.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Descent to a magnetization-minimal representative -/

set_option linter.unusedDecidableInType false in
/-- Iterate the full parity-block step-down until the magnetization sum drops below `2`. -/
theorem parityReachableS_to_min_magSum_of_connected
    {G : SimpleGraph V} (hG : G.Connected) (hN : 1 ≤ N) (σ : V → Fin (N + 1)) :
    ∃ σ_min : V → Fin (N + 1),
      magSumS σ_min < 2 ∧ ParityReachableS G σ σ_min := by
  suffices h : ∀ (n : ℕ) (τ : V → Fin (N + 1)), magSumS τ = n →
      ∃ σ_min : V → Fin (N + 1), magSumS σ_min < 2 ∧ ParityReachableS G τ σ_min from
    h (magSumS σ) σ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro τ hmag
    by_cases hsmall : n < 2
    · exact ⟨τ, by omega, ParityReachableS.refl G τ⟩
    · obtain ⟨τ', h_mag', h_reach⟩ :=
        parityReachableS_step_down_of_connected hG hN (by omega : 2 ≤ magSumS τ)
      obtain ⟨σ_min, h_min_small, h_min_reach⟩ := ih (magSumS τ') (by omega) τ' rfl
      exact ⟨σ_min, h_min_small, h_reach.trans h_min_reach⟩

set_option linter.unusedDecidableInType false in
/-- Iterate the ion-only step-down until the magnetization sum drops below `2`. -/
theorem ionParityReachableS_to_min_magSum_of_connected
    {G : SimpleGraph V} (hG : G.Connected) (hN : 2 ≤ N) (σ : V → Fin (N + 1)) :
    ∃ σ_min : V → Fin (N + 1),
      magSumS σ_min < 2 ∧ IonParityReachableS G σ σ_min := by
  suffices h : ∀ (n : ℕ) (τ : V → Fin (N + 1)), magSumS τ = n →
      ∃ σ_min : V → Fin (N + 1), magSumS σ_min < 2 ∧ IonParityReachableS G τ σ_min from
    h (magSumS σ) σ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro τ hmag
    by_cases hsmall : n < 2
    · exact ⟨τ, by omega, IonParityReachableS.refl G τ⟩
    · obtain ⟨τ', h_mag', h_reach⟩ :=
        ionParityReachableS_step_down_of_connected hG hN (by omega : 2 ≤ magSumS τ)
      obtain ⟨σ_min, h_min_small, h_min_reach⟩ := ih (magSumS τ') (by omega) τ' rfl
      exact ⟨σ_min, h_min_small, h_reach.trans h_min_reach⟩

set_option linter.unusedDecidableInType false in
/-- Iterate the bond-only step-down until the magnetization sum drops below `2`. -/
theorem bondParityReachableS_to_min_magSum_of_connected
    {G : SimpleGraph V} (hV : Nontrivial V) (hG : G.Connected) (hN : 1 ≤ N)
    (σ : V → Fin (N + 1)) :
    ∃ σ_min : V → Fin (N + 1),
      magSumS σ_min < 2 ∧ BondParityReachableS G σ σ_min := by
  suffices h : ∀ (n : ℕ) (τ : V → Fin (N + 1)), magSumS τ = n →
      ∃ σ_min : V → Fin (N + 1), magSumS σ_min < 2 ∧ BondParityReachableS G τ σ_min from
    h (magSumS σ) σ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro τ hmag
    by_cases hsmall : n < 2
    · exact ⟨τ, by omega, BondParityReachableS.refl G τ⟩
    · obtain ⟨τ', h_mag', h_reach⟩ :=
        bondParityReachableS_step_down_of_connected hV hG hN (by omega : 2 ≤ magSumS τ)
      obtain ⟨σ_min, h_min_small, h_min_reach⟩ := ih (magSumS τ') (by omega) τ' rfl
      exact ⟨σ_min, h_min_small, h_reach.trans h_min_reach⟩

/-! ## Totality on a connected graph -/

set_option linter.unusedDecidableInType false in
/-- **Full parity-block reachability totality on a connected graph**: on a connected `G` with
`1 ≤ N`, any two configurations of the same total-magnetization parity are connected by
parity-block moves.  No bipartiteness and no balanced-sublattice hypothesis. -/
theorem parityReachableS_total_of_connected
    {G : SimpleGraph V} (hG : G.Connected) (hN : 1 ≤ N)
    {σ σ' : V → Fin (N + 1)}
    (h_par : magSumS σ % 2 = magSumS σ' % 2) :
    ParityReachableS G σ σ' := by
  obtain ⟨σ_min, h_min_lt, h_reach_min⟩ :=
    parityReachableS_to_min_magSum_of_connected hG hN σ
  obtain ⟨σ'_min, h'_min_lt, h'_reach_min⟩ :=
    parityReachableS_to_min_magSum_of_connected hG hN σ'
  have h_par_min : magSumS σ_min = magSumS σ'_min := by
    have h1 := parityReachableS_magSumS_parity_eq h_reach_min
    have h2 := parityReachableS_magSumS_parity_eq h'_reach_min
    omega
  have h_within : ParityReachableS G σ_min σ'_min :=
    parityReachableS_of_raiseLowerReachableS
      (raiseLowerReachableS_of_connected G hG h_par_min)
  exact (h_reach_min.trans h_within).trans (parityReachableS_symm h'_reach_min)

set_option linter.unusedDecidableInType false in
/-- **Ion-only parity reachability totality on a connected graph**: on a connected `G` with
`2 ≤ N`, any two configurations of the same total-magnetization parity are connected by
transverse and single-ion moves.  `2 ≤ N` is necessary: at `N = 1` the single-ion `±2` move is
never available, so the relation reduces to the magnetization-preserving transverse moves and
cannot change the magnetization sum at all. -/
theorem ionParityReachableS_total_of_connected
    {G : SimpleGraph V} (hG : G.Connected) (hN : 2 ≤ N)
    {σ σ' : V → Fin (N + 1)}
    (h_par : magSumS σ % 2 = magSumS σ' % 2) :
    IonParityReachableS G σ σ' := by
  obtain ⟨σ_min, h_min_lt, h_reach_min⟩ :=
    ionParityReachableS_to_min_magSum_of_connected hG hN σ
  obtain ⟨σ'_min, h'_min_lt, h'_reach_min⟩ :=
    ionParityReachableS_to_min_magSum_of_connected hG hN σ'
  have h_par_min : magSumS σ_min = magSumS σ'_min := by
    have h1 := parityReachableS_magSumS_parity_eq
      (IonParityReachableS.to_parityReachableS h_reach_min)
    have h2 := parityReachableS_magSumS_parity_eq
      (IonParityReachableS.to_parityReachableS h'_reach_min)
    omega
  have h_within : IonParityReachableS G σ_min σ'_min :=
    IonParityReachableS.of_raiseLowerReachable
      (raiseLowerReachableS_of_connected G hG h_par_min)
  exact (h_reach_min.trans h_within).trans (IonParityReachableS.symm h'_reach_min)

set_option linter.unusedDecidableInType false in
/-- **Bond-only parity reachability totality on a connected graph**: on a connected `G` with at
least two vertices and `1 ≤ N`, any two configurations of the same total-magnetization parity
are connected by transverse and bond-parity moves.  `Nontrivial V` is necessary here and not on
the other two relations: on the one-vertex connected graph with `N = 2`, the configurations
`σ = (2)` and `σ' = (0)` have equal parity and are related by a single-ion `±2` move, but the
bond-only relation has no move at all there, both of its step kinds requiring an edge. -/
theorem bondParityReachableS_total_of_connected
    {G : SimpleGraph V} (hV : Nontrivial V) (hG : G.Connected) (hN : 1 ≤ N)
    {σ σ' : V → Fin (N + 1)}
    (h_par : magSumS σ % 2 = magSumS σ' % 2) :
    BondParityReachableS G σ σ' := by
  obtain ⟨σ_min, h_min_lt, h_reach_min⟩ :=
    bondParityReachableS_to_min_magSum_of_connected hV hG hN σ
  obtain ⟨σ'_min, h'_min_lt, h'_reach_min⟩ :=
    bondParityReachableS_to_min_magSum_of_connected hV hG hN σ'
  have h_par_min : magSumS σ_min = magSumS σ'_min := by
    have h1 := parityReachableS_magSumS_parity_eq
      (BondParityReachableS.to_parityReachableS h_reach_min)
    have h2 := parityReachableS_magSumS_parity_eq
      (BondParityReachableS.to_parityReachableS h'_reach_min)
    omega
  have h_within : BondParityReachableS G σ_min σ'_min :=
    BondParityReachableS.of_raiseLowerReachable
      (raiseLowerReachableS_of_connected G hG h_par_min)
  exact (h_reach_min.trans h_within).trans (BondParityReachableS.symm h'_reach_min)

end LatticeSystem.Quantum
