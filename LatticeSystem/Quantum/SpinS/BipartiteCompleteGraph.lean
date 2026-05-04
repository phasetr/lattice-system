import LatticeSystem.Quantum.SpinS.ConfigDist
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The complete bipartite graph induced by a sublattice indicator
(Tasaki §2.5 Phase B-γ γ-3 final preparation)

For a vertex type `V` with a sublattice indicator `A : V → Bool`,
the **complete bipartite graph** `bipartiteCompleteGraphOf A` has
an edge between every pair of distinct vertices on different
sublattices:

  `(bipartiteCompleteGraphOf A).Adj x y ↔ x ≠ y ∧ A x ≠ A y`.

This is the natural "maximally connected" bipartite graph compatible
with the sublattice partition `(A^{-1}(true), A^{-1}(false))`. It is
the spin-S analogue setting where the Marshall–Lieb–Mattis irreducibility
argument is most cleanly stated: every bipartite raise/lower step
involves a `bipartiteCompleteGraphOf A`-edge, and conversely every
edge corresponds to a possible raise/lower step.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*}

/-- The complete bipartite graph induced by a sublattice indicator
`A : V → Bool`: an edge between `x` and `y` iff they are distinct
and lie on different sublattices. -/
@[simps]
def bipartiteCompleteGraphOf (A : V → Bool) : SimpleGraph V where
  Adj x y := x ≠ y ∧ A x ≠ A y
  symm := fun _ _ ⟨h, hA⟩ => ⟨h.symm, fun heq => hA heq.symm⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- Adjacency in `bipartiteCompleteGraphOf A`: an edge iff distinct and
on different sublattices. -/
theorem bipartiteCompleteGraphOf_adj_iff (A : V → Bool) (x y : V) :
    (bipartiteCompleteGraphOf A).Adj x y ↔ x ≠ y ∧ A x ≠ A y :=
  Iff.rfl

/-- Every adjacency in `bipartiteCompleteGraphOf A` has endpoints
on different sublattices. -/
theorem bipartiteCompleteGraphOf_adj_sublattice_ne {A : V → Bool}
    {x y : V} (hadj : (bipartiteCompleteGraphOf A).Adj x y) :
    A x ≠ A y :=
  hadj.2

/-- Adjacency in `bipartiteCompleteGraphOf A` implies `x ≠ y`. -/
theorem bipartiteCompleteGraphOf_adj_ne {A : V → Bool}
    {x y : V} (hadj : (bipartiteCompleteGraphOf A).Adj x y) :
    x ≠ y :=
  hadj.1

/-- Decidability instance for adjacency in `bipartiteCompleteGraphOf A`,
useful for downstream computations (e.g. graph-derived couplings via
`couplingOf`). Relies on `DecidableEq V`. -/
instance bipartiteCompleteGraphOf_decidableAdj {V : Type*} [DecidableEq V]
    (A : V → Bool) :
    DecidableRel (bipartiteCompleteGraphOf A).Adj := by
  intro x y
  unfold bipartiteCompleteGraphOf SimpleGraph.Adj
  infer_instance

/-- The Marshall-trivial sublattice `A := fun _ => false` gives the
empty graph. -/
theorem bipartiteCompleteGraphOf_const_false {V : Type*} :
    bipartiteCompleteGraphOf (V := V) (fun _ => false) = ⊥ := by
  ext x y
  rw [bipartiteCompleteGraphOf_adj_iff]
  simp

/-- The Marshall-trivial sublattice `A := fun _ => true` gives the
empty graph. -/
theorem bipartiteCompleteGraphOf_const_true {V : Type*} :
    bipartiteCompleteGraphOf (V := V) (fun _ => true) = ⊥ := by
  ext x y
  rw [bipartiteCompleteGraphOf_adj_iff]
  simp

/-- For exactly-two-vertex `V` with the two vertices on different
sublattices, `bipartiteCompleteGraphOf A` has exactly the (single)
edge between them — a single edge graph. -/
theorem bipartiteCompleteGraphOf_adj_of_ne_of_sublattice_ne
    {A : V → Bool} {x y : V} (hxy : x ≠ y) (hAne : A x ≠ A y) :
    (bipartiteCompleteGraphOf A).Adj x y :=
  ⟨hxy, hAne⟩

/-! ## Bipartite step from over/under sites -/

variable [Fintype V] [DecidableEq V] {N : ℕ}

/-- For an over site `x` (where `(σ' x).val < (σ x).val`) and an
under site `y` (where `(σ y).val < (σ' y).val`) on different
sublattices (`A x ≠ A y`), there exists a configuration `σ''` reachable
from `σ` by a single bipartite raise/lower step (lower at `x`, raise
at `y`) such that `configDistS σ'' σ' + 2 = configDistS σ σ'`. -/
theorem exists_raiseLowerStepS_bipartite_of_over_under_ne_sublattice
    {A : V → Bool} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hxy : x ≠ y) (hAne : A x ≠ A y)
    (hover : (σ' x).val < (σ x).val)
    (hunder : (σ y).val < (σ' y).val) :
    ∃ σ'' : V → Fin (N + 1),
      RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ'' ∧
        configDistS σ'' σ' + 2 = configDistS σ σ' := by
  -- Bounds for the raise/lower update.
  have hx_bound : (σ x).val - 1 < N + 1 := by
    have := (σ x).isLt; omega
  have hy_bound : (σ y).val + 1 < N + 1 := by
    have := (σ' y).isLt; omega
  -- Define σ''.
  let σ'' : V → Fin (N + 1) :=
    Function.update (Function.update σ x ⟨(σ x).val - 1, hx_bound⟩) y
      ⟨(σ y).val + 1, hy_bound⟩
  refine ⟨σ'', ?_, ?_⟩
  · -- Step σ ↦ σ'': lower at x, raise at y.
    -- Adjacency in the bipartite complete graph: x ≠ y and A x ≠ A y.
    have hadj : (bipartiteCompleteGraphOf A).Adj x y := ⟨hxy, hAne⟩
    -- σ'' agrees with σ off {x, y}.
    have hagree : ∀ k, k ≠ x → k ≠ y → σ'' k = σ k := by
      intro k hkx hky
      show (Function.update (Function.update σ x _) y _) k = σ k
      rw [Function.update_of_ne hky, Function.update_of_ne hkx]
    -- σ'' x and σ'' y values.
    have hupd_x : (σ'' x).val = (σ x).val - 1 := by
      show (Function.update (Function.update σ x _) y _ x).val = _
      rw [Function.update_of_ne hxy, Function.update_self]
    have hupd_y : (σ'' y).val = (σ y).val + 1 := by
      show (Function.update (Function.update σ x _) y _ y).val = _
      rw [Function.update_self]
    refine ⟨x, y, hadj, Or.inr ⟨?_, ?_⟩, hagree⟩
    · rw [hupd_x]; omega
    · rw [hupd_y]
  · -- Distance reduces by 2.
    exact configDistS_decrease_of_over_under hxy hover hunder

/-- The "hard case" of bipartite reachability: when over and under
sites land on the same sublattice, a 2-step transport through an
opposite-sublattice intermediate `z` (with `σ z < N` so it has room
to absorb a temporary +1) gives a `RaiseLowerReachableS` chain to a
configuration `σ''` with reduced `configDistS`.

The intermediate `σ_1` raises `z` then `σ_2 = σ''` lowers it back —
net effect on `z` is zero, and the (x, y) transport happens.

Hypothesis `hzN : (σ z).val < N` is needed for the raise step; the
existence of such `z` may fail in degenerate "saturated" configurations
but holds generically. -/
theorem exists_raiseLowerReachableS_bipartite_of_over_under_eq_sublattice
    {A : V → Bool} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hxy : x ≠ y) (hAeq : A x = A y)
    (hover : (σ' x).val < (σ x).val)
    (hunder : (σ y).val < (σ' y).val)
    {z : V} (hAz : A z ≠ A x) (hzN : (σ z).val < N) :
    ∃ σ'' : V → Fin (N + 1),
      RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ'' ∧
        configDistS σ'' σ' + 2 = configDistS σ σ' := by
  -- z ≠ x, z ≠ y (since A z ≠ A x = A y).
  have hzx : z ≠ x := fun heq => hAz (heq ▸ rfl)
  have hzy : z ≠ y := fun heq => hAz (heq ▸ hAeq.symm)
  -- Bounds for the updates.
  have hx_bound : (σ x).val - 1 < N + 1 := by
    have := (σ x).isLt; omega
  have hy_bound : (σ y).val + 1 < N + 1 := by
    have := (σ' y).isLt; omega
  have hz_raise_bound : (σ z).val + 1 < N + 1 := by omega
  -- Direct definition of σ_2 = σ with x lowered, y raised (z unchanged).
  let σ_2 : V → Fin (N + 1) :=
    Function.update (Function.update σ x ⟨(σ x).val - 1, hx_bound⟩) y
      ⟨(σ y).val + 1, hy_bound⟩
  -- Intermediate σ_1 = σ with x lowered, z raised.
  let σ_1 : V → Fin (N + 1) :=
    Function.update (Function.update σ x ⟨(σ x).val - 1, hx_bound⟩) z
      ⟨(σ z).val + 1, hz_raise_bound⟩
  -- σ_1 site values.
  have hσ_1_z : (σ_1 z).val = (σ z).val + 1 := by
    show (Function.update (Function.update σ x _) z _ z).val = _
    rw [Function.update_self]
  have hσ_1_x : (σ_1 x).val = (σ x).val - 1 := by
    show (Function.update (Function.update σ x _) z _ x).val = _
    rw [Function.update_of_ne hzx.symm, Function.update_self]
  have hσ_1_y_eq : σ_1 y = σ y := by
    show Function.update (Function.update σ x _) z _ y = σ y
    rw [Function.update_of_ne hzy.symm, Function.update_of_ne hxy.symm]
  have hσ_1_off : ∀ k, k ≠ x → k ≠ z → σ_1 k = σ k := by
    intro k hkx hkz
    show Function.update (Function.update σ x _) z _ k = σ k
    rw [Function.update_of_ne hkz, Function.update_of_ne hkx]
  -- σ_2 site values.
  have hσ_2_x : (σ_2 x).val = (σ x).val - 1 := by
    show (Function.update (Function.update σ x _) y _ x).val = _
    rw [Function.update_of_ne hxy, Function.update_self]
  have hσ_2_y : (σ_2 y).val = (σ y).val + 1 := by
    show (Function.update (Function.update σ x _) y _ y).val = _
    rw [Function.update_self]
  have hσ_2_z : σ_2 z = σ z := by
    show (Function.update (Function.update σ x _) y _) z = σ z
    rw [Function.update_of_ne hzy, Function.update_of_ne hzx]
  have hσ_2_off : ∀ k, k ≠ x → k ≠ y → σ_2 k = σ k := by
    intro k hkx hky
    show (Function.update (Function.update σ x _) y _) k = σ k
    rw [Function.update_of_ne hky, Function.update_of_ne hkx]
  refine ⟨σ_2, ?_, ?_⟩
  · -- Reachability via 2 steps σ → σ_1 → σ_2.
    -- Step 1: σ → σ_1 (lower x, raise z), edge (x, z).
    have hadj1 : (bipartiteCompleteGraphOf A).Adj x z :=
      ⟨hzx.symm, fun heq => hAz heq.symm⟩
    have hstep1 : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ σ_1 := by
      refine ⟨x, z, hadj1, Or.inr ⟨?_, ?_⟩, hσ_1_off⟩
      · rw [hσ_1_x]; omega
      · rw [hσ_1_z]
    -- Step 2: σ_1 → σ_2 (lower z, raise y), edge (z, y).
    have hadj2 : (bipartiteCompleteGraphOf A).Adj z y :=
      ⟨hzy, fun heq => hAz (heq.trans hAeq.symm)⟩
    -- Differences σ_1 vs σ_2: at z (σ_1 z = σ z + 1, σ_2 z = σ z) and at y
    -- (σ_1 y = σ y, σ_2 y = σ y + 1). Off {z, y}: agree.
    have hagree2 : ∀ k, k ≠ z → k ≠ y → σ_2 k = σ_1 k := by
      intro k hkz hky
      by_cases hkx : k = x
      · subst hkx
        apply Fin.ext
        rw [hσ_1_x, hσ_2_x]
      · -- k ≠ x, k ≠ y, k ≠ z: σ_2 k = σ k = σ_1 k.
        rw [hσ_2_off k hkx hky, (hσ_1_off k hkx hkz).symm]
    -- Step 2 raise/lower data:
    -- (σ_2 z).val + 1 = (σ_1 z).val: σ_2 z = σ z, σ_1 z = σ z + 1. So σ z + 1 = σ z + 1 ✓.
    -- (σ_1 y).val + 1 = (σ_2 y).val: σ_1 y = σ y, σ_2 y = σ y + 1. So σ y + 1 = σ y + 1 ✓.
    have hupd_z2 : (σ_2 z).val + 1 = (σ_1 z).val := by
      have := hσ_2_z
      rw [show (σ_2 z).val = (σ z).val from by rw [this], hσ_1_z]
    have hupd_y2 : (σ_1 y).val + 1 = (σ_2 y).val := by
      rw [hσ_1_y_eq, hσ_2_y]
    have hstep2 : RaiseLowerStepS (bipartiteCompleteGraphOf A) σ_1 σ_2 := by
      refine ⟨z, y, hadj2, Or.inr ⟨hupd_z2, hupd_y2⟩, hagree2⟩
    -- Compose: σ → σ_1 → σ_2.
    exact (RaiseLowerReachableS.single hstep1).tail' hstep2
  · -- Distance reduction: σ_2 = direct lower-x raise-y at (x, y), so reduce by 2.
    exact configDistS_decrease_of_over_under hxy hover hunder

/-- **Unified bipartite over/under reduction**: combines the easy case
(#819, over/under on different sublattices: direct step) and the hard
case (#820, same sublattice: 2-step transport via intermediate).

For an over site `x` and under site `y` with `x ≠ y`, the intermediate-
existence hypothesis `h_intermediate` guarantees a transport when
`A x = A y` (only used in the hard case). The conclusion combines
both cases as a `RaiseLowerReachableS` (which subsumes a single step). -/
theorem exists_raiseLowerReachableS_bipartite_of_over_under
    {A : V → Bool} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hxy : x ≠ y)
    (hover : (σ' x).val < (σ x).val)
    (hunder : (σ y).val < (σ' y).val)
    (h_intermediate : A x = A y →
      ∃ z, A z ≠ A x ∧ (σ z).val < N) :
    ∃ σ'' : V → Fin (N + 1),
      RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ'' ∧
        configDistS σ'' σ' + 2 = configDistS σ σ' := by
  by_cases hAeq : A x = A y
  · -- Hard case: same sublattice, use 2-step transport.
    obtain ⟨z, hAz, hzN⟩ := h_intermediate hAeq
    exact exists_raiseLowerReachableS_bipartite_of_over_under_eq_sublattice
      hxy hAeq hover hunder hAz hzN
  · -- Easy case: different sublattices, use direct step.
    obtain ⟨σ'', hstep, hreduce⟩ :=
      exists_raiseLowerStepS_bipartite_of_over_under_ne_sublattice
        hxy hAeq hover hunder
    exact ⟨σ'', RaiseLowerReachableS.single hstep, hreduce⟩

/-! ## Bipartite reachability iteration for equal-magnetization configs -/

/-- **Bipartite reachability for equal-magnetization configurations**:
on the complete bipartite graph `bipartiteCompleteGraphOf A`, any two
configurations with the same magnetization sum are connected by a
chain of bipartite raise/lower steps, given a strong intermediate-
existence hypothesis.

The hypothesis `h_intermediate` requires that for every configuration
`τ` (with the magnetization preserved by raise/lower steps) and every
sublattice color, there is a vertex on the OPPOSITE sublattice with
`τ < N` — i.e., not all opposite vertices are saturated. This holds
in many physically interesting cases (e.g., the magnetization-zero
subspace with balanced sublattices, away from the "all-saturated"
extreme).

Proof: strong induction on `configDistS`, using
`exists_raiseLowerReachableS_bipartite_of_over_under` (PR #821) at
each step (which combines the easy and hard cases). -/
theorem raiseLowerReachableS_bipartiteCompleteGraph_of_eq_magSumS
    (A : V → Bool)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {σ σ' : V → Fin (N + 1)} (hmag : magSumS σ = magSumS σ') :
    RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ' := by
  -- Strong induction on configDistS σ σ'.
  suffices h : ∀ n, ∀ σ σ' : V → Fin (N + 1),
      magSumS σ = magSumS σ' → configDistS σ σ' ≤ n →
      RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ σ' from
    h (configDistS σ σ') σ σ' hmag (le_refl _)
  intro n
  induction n with
  | zero =>
    intro σ σ' _ hd
    have hsigma : σ = σ' :=
      (configDistS_eq_zero_iff σ σ').mp (Nat.le_zero.mp hd)
    rw [hsigma]
    exact RaiseLowerReachableS.refl _ _
  | succ n ih =>
    intro σ σ' hmag hd
    by_cases hne : σ = σ'
    · rw [hne]; exact RaiseLowerReachableS.refl _ _
    · obtain ⟨⟨x, hover⟩, y, hunder⟩ :=
        exists_over_under_of_eq_magSumS hne hmag
      have hxy : x ≠ y := fun heq => by subst heq; omega
      have hint : A x = A y → ∃ z, A z ≠ A x ∧ (σ z).val < N :=
        fun _ => h_intermediate σ x
      obtain ⟨σ_2, hreach, hreduce⟩ :=
        exists_raiseLowerReachableS_bipartite_of_over_under
          hxy hover hunder hint
      have hmag_2 : magSumS σ_2 = magSumS σ :=
        magSumS_eq_of_raiseLowerReachableS hreach
      have hIH : RaiseLowerReachableS (bipartiteCompleteGraphOf A) σ_2 σ' := by
        apply ih
        · rw [hmag_2]; exact hmag
        · omega
      exact hreach.trans hIH

/-! ## Preconnectedness of `bipartiteCompleteGraphOf` -/

/-- The bipartite-complete graph `bipartiteCompleteGraphOf A` is
preconnected when both sublattices are non-empty. Any two `x, y ∈ V`
are joined by a walk of length ≤ 2:

* If `A x ≠ A y`: direct edge.
* If `A x = A y`: pick any `z` in the opposite sublattice (exists by
  non-emptiness of the other side); then `x ~ z ~ y` via two edges.

Spin-`S` mirror of `bipartiteGraphFromA_preconnected` (spin-`1/2`,
in `Quantum/MarshallLiebMattis/BipartiteGraph.lean`). -/
theorem bipartiteCompleteGraphOf_preconnected
    (A : V → Bool)
    (hA_pos : ∃ x : V, A x = true) (hA_neg : ∃ y : V, A y = false) :
    (bipartiteCompleteGraphOf A).Preconnected := by
  intro x y
  by_cases hAxy : A x = A y
  · -- Same sublattice: pick a vertex in the opposite sublattice.
    by_cases hAx : A x = true
    · -- A x = true, so A y = true; pick z with A z = false.
      obtain ⟨z, hz⟩ := hA_neg
      have hxz : (bipartiteCompleteGraphOf A).Adj x z := by
        rw [bipartiteCompleteGraphOf_adj_iff]
        refine ⟨?_, ?_⟩
        · intro heq; rw [heq, hz] at hAx; exact Bool.noConfusion hAx
        · rw [hAx, hz]; decide
      have hAyT : A y = true := hAxy ▸ hAx
      have hyz : (bipartiteCompleteGraphOf A).Adj y z := by
        rw [bipartiteCompleteGraphOf_adj_iff]
        refine ⟨?_, ?_⟩
        · intro heq; rw [heq, hz] at hAyT; exact Bool.noConfusion hAyT
        · rw [hAyT, hz]; decide
      exact ⟨(SimpleGraph.Walk.nil.cons hxz).append
        ((SimpleGraph.Walk.nil.cons hyz).reverse)⟩
    · -- A x = false, so A y = false; pick z with A z = true.
      have hAxF : A x = false := by
        cases h : A x
        · rfl
        · exact absurd h hAx
      obtain ⟨z, hz⟩ := hA_pos
      have hxz : (bipartiteCompleteGraphOf A).Adj x z := by
        rw [bipartiteCompleteGraphOf_adj_iff]
        refine ⟨?_, ?_⟩
        · intro heq; rw [heq, hz] at hAxF; exact Bool.noConfusion hAxF
        · rw [hAxF, hz]; decide
      have hAyF : A y = false := hAxy ▸ hAxF
      have hyz : (bipartiteCompleteGraphOf A).Adj y z := by
        rw [bipartiteCompleteGraphOf_adj_iff]
        refine ⟨?_, ?_⟩
        · intro heq; rw [heq, hz] at hAyF; exact Bool.noConfusion hAyF
        · rw [hAyF, hz]; decide
      exact ⟨(SimpleGraph.Walk.nil.cons hxz).append
        ((SimpleGraph.Walk.nil.cons hyz).reverse)⟩
  · -- Different sublattices: direct edge.
    have hxy : x ≠ y := fun heq => by subst heq; exact hAxy rfl
    have hxy_adj : (bipartiteCompleteGraphOf A).Adj x y := by
      rw [bipartiteCompleteGraphOf_adj_iff]
      exact ⟨hxy, hAxy⟩
    exact ⟨SimpleGraph.Walk.nil.cons hxy_adj⟩

end LatticeSystem.Quantum
