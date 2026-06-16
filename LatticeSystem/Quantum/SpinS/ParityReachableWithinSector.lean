import LatticeSystem.Quantum.SpinS.ParityReachable
import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraph

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Within-sector reachability lifted to `ParityReachableS`

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The transverse hop is one of the three elementary parity-block moves
(`ParityStepS = RaiseLowerStepS ∨ ParityBondStepS ∨ SingleIonStepS`), so
`RaiseLowerStepS ⊆ ParityStepS` and consequently `RaiseLowerReachableS ⊆
ParityReachableS`.  This lifts the within-sector `RaiseLowerReachableS`
totality for the bipartite complete graph (Tasaki §2.3, file
`BipartiteCompleteGraph.lean`) to `ParityReachableS`, the relation we
need for (d) reachability totality of the parity-block matrix
irreducibility (#3797).

Together with the cross-sector bridging machinery to be added in
follow-up PRs (single-ion / bond-parity moves that step between
adjacent magnetization sectors at the same parity), this provides the
within-sector half of (d.3) full reachability.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [Fintype V] [DecidableEq V] in
/-- **Single-step lift**: a `RaiseLowerStepS` is a `ParityStepS`. -/
theorem ParityStepS.of_raiseLower {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    (h : RaiseLowerStepS G σ σ') : ParityStepS G σ σ' :=
  Or.inl h

omit [Fintype V] [DecidableEq V] in
/-- **Lift `RaiseLowerReachableS → ParityReachableS`**: every transverse-only reachability
chain is also a parity-block reachability chain (via the `Or.inl` injection of
`RaiseLowerStepS` into `ParityStepS`). -/
theorem parityReachableS_of_raiseLowerReachableS {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    (h : RaiseLowerReachableS G σ σ') : ParityReachableS G σ σ' := by
  refine Relation.ReflTransGen.mono ?_ h
  intro a b hab
  exact ParityStepS.of_raiseLower hab

omit [DecidableEq V] in
/-- **Within-sector ParityReachableS on the bipartite complete graph**: any two
configurations sharing the same total magnetization are `ParityReachableS`-connected.

Lifts `raiseLowerReachableS_bipartiteCompleteGraph_of_eq_magSumS_legacy` through the inclusion
`RaiseLowerStepS ⊆ ParityStepS`. -/
theorem parityReachableS_bipartiteCompleteGraph_of_eq_magSumS
    (A : V → Bool)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {σ σ' : V → Fin (N + 1)} (hmag : magSumS σ = magSumS σ') :
    ParityReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  classical
  exact parityReachableS_of_raiseLowerReachableS
    (raiseLowerReachableS_bipartiteCompleteGraph_of_eq_magSumS_legacy A h_intermediate hmag)

end LatticeSystem.Quantum
