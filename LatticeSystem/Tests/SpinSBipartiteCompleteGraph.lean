import LatticeSystem.Quantum.SpinS.BipartiteCompleteGraph

/-!
# Test coverage for the spin-`S` bipartite complete graph
(Tasaki §2.5 Phase B-γ γ-3 final prep)
-/

namespace LatticeSystem.Tests.SpinSBipartiteCompleteGraph

open LatticeSystem.Quantum

variable {V : Type*}

/-- Adjacency in `bipartiteCompleteGraphOf A` is `x ≠ y ∧ A x ≠ A y`. -/
example (A : V → Bool) (x y : V) :
    (bipartiteCompleteGraphOf A).Adj x y ↔ x ≠ y ∧ A x ≠ A y :=
  bipartiteCompleteGraphOf_adj_iff A x y

/-- Adjacency implies different sublattices. -/
example {A : V → Bool} {x y : V}
    (hadj : (bipartiteCompleteGraphOf A).Adj x y) :
    A x ≠ A y :=
  bipartiteCompleteGraphOf_adj_sublattice_ne hadj

/-- Adjacency implies distinct vertices. -/
example {A : V → Bool} {x y : V}
    (hadj : (bipartiteCompleteGraphOf A).Adj x y) :
    x ≠ y :=
  bipartiteCompleteGraphOf_adj_ne hadj

/-- Trivial sublattice (constant `false`) gives the empty graph. -/
example : bipartiteCompleteGraphOf (V := V) (fun _ => false) = ⊥ :=
  bipartiteCompleteGraphOf_const_false

/-- Trivial sublattice (constant `true`) gives the empty graph. -/
example : bipartiteCompleteGraphOf (V := V) (fun _ => true) = ⊥ :=
  bipartiteCompleteGraphOf_const_true

/-- Direct adjacency from distinct vertices on different sublattices. -/
example {A : V → Bool} {x y : V} (hxy : x ≠ y) (hAne : A x ≠ A y) :
    (bipartiteCompleteGraphOf A).Adj x y :=
  bipartiteCompleteGraphOf_adj_of_ne_of_sublattice_ne hxy hAne

/-- Easy case: bipartite step from over/under on different sublattices. -/
example {N : ℕ} [Fintype V] [DecidableEq V] {A : V → Bool}
    {σ σ' : V → Fin (N + 1)}
    {x y : V} (hxy : x ≠ y) (hAne : A x ≠ A y)
    (hover : (σ' x).val < (σ x).val)
    (hunder : (σ y).val < (σ' y).val) :
    ∃ σ'' : V → Fin (N + 1),
      RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ'' ∧
        configDistS σ'' σ' + 2 = configDistS σ σ' :=
  exists_raiseLowerStepS_bipartite_of_over_under_ne_sublattice hxy hAne hover hunder

/-- Hard case: 2-step transport for over/under on same sublattice. -/
example {N : ℕ} [Fintype V] [DecidableEq V] {A : V → Bool}
    {σ σ' : V → Fin (N + 1)}
    {x y : V} (hxy : x ≠ y) (hAeq : A x = A y)
    (hover : (σ' x).val < (σ x).val)
    (hunder : (σ y).val < (σ' y).val)
    {z : V} (hAz : A z ≠ A x) (hzN : (σ z).val < N) :
    ∃ σ'' : V → Fin (N + 1),
      RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ'' ∧
        configDistS σ'' σ' + 2 = configDistS σ σ' :=
  exists_raiseLowerReachableS_bipartite_of_over_under_eq_sublattice
    hxy hAeq hover hunder hAz hzN

/-- Unified bipartite over/under reduction. -/
example {N : ℕ} [Fintype V] [DecidableEq V] {A : V → Bool}
    {σ σ' : V → Fin (N + 1)}
    {x y : V} (hxy : x ≠ y)
    (hover : (σ' x).val < (σ x).val)
    (hunder : (σ y).val < (σ' y).val)
    (h_intermediate : A x = A y →
      ∃ z, A z ≠ A x ∧ (σ z).val < N) :
    ∃ σ'' : V → Fin (N + 1),
      RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ'' ∧
        configDistS σ'' σ' + 2 = configDistS σ σ' :=
  exists_raiseLowerReachableS_bipartite_of_over_under hxy hover hunder
    h_intermediate

/-- Bipartite reachability for equal-magnetization configurations. -/
example {N : ℕ} [Fintype V] [DecidableEq V] (A : V → Bool)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {σ σ' : V → Fin (N + 1)} (hmag : magSumS σ = magSumS σ') :
    RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ' :=
  raiseLowerReachableS_bipartiteCompleteGraph_of_eq_magSumS A h_intermediate hmag

end LatticeSystem.Tests.SpinSBipartiteCompleteGraph
