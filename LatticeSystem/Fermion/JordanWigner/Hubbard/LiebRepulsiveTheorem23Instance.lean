import LatticeSystem.Quantum.SpinS.Theorem23StructuralGeneralFinal
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveFermionSpinBridge
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveFermionSpinCasimirBridge

/-!
# Theorem 2.3 instance for Theorem 10.4 (PR-10b scaffold, Issue #5320)

**Status: Red scaffold.** Every declaration below is a `sorry`-stub type signature; no proof
content has been supplied yet. This file records the bridging-lemma shape agreed in the PR-10b
design round (`.self-local/active/issue-5320.md`, "PR-10 through PR-14 design round" section) for
instantiating

`tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`
(`Quantum/SpinS/Theorem23StructuralGeneralFinal.lean:40`)

at `J = (2 : ℂ) • bipartiteCoupling A'`, `N_spin = 1`, and connecting the resulting Marshall-
positive ground state and its total-spin Casimir eigenvalue to Theorem 10.4's target Casimir
(`liebRepulsiveSpinCasimir A`, `LiebRepulsive.lean:55`) via PR-9a's Hamiltonian bridge
(`secondOrderEffectiveHamiltonian_liebPerturbation_reindex_eq_heisenbergOnMagSector`,
`LiebRepulsiveFermionSpinBridge.lean`) and PR-9b's Casimir bridge
(`fermionTotalSpinSquared_reindex_eq_totalSpinSSquaredOnMagSector`,
`LiebRepulsiveFermionSpinCasimirBridge.lean`).

## Scope

This scaffold covers only the **nondegenerate** bipartition case (`1 ≤ |A|`, `1 ≤ |¬A|`). The fully
polarised endpoints `A = ∅` / `A = Finset.univ` are Theorem 2.3's own out-of-reach cases (its
`hsB`/`1 ≤ |¬A|` side conditions fail there) and are deferred to a later PR in the arc (PR-12/PR-14
per the design note), to be proved directly as the fully polarised ground state
`S₀ = (N+1)/2`. The model-specific sector-bridge work connecting `configSector`/
`numberSpinZSectorEuclidean`/`spinZSectorEuclidean` (PR-11's responsibility) is likewise out of
scope here; the lemmas below stay entirely on the `heisenbergHamiltonianSMatrixOnMagSector`/
`fermionTotalSpinSquared` side of that boundary.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.3, p. 42; §10.2.2 Theorem 10.4, p. 350.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-! ## Orientation adapter (`horient`)

Theorem 2.3 is stated under the canonical orientation `|¬A| ≤ |A|`
(`Theorem23StructuralGeneralFinal.lean:42`), while Theorem 10.4's target
(`sublatticeImbalance`, `LiebRepulsive.lean:50`) is `Int.natAbs`-based and orientation-agnostic. The
following adapter swaps `A` for its complement when needed, and records that every downstream
quantity (imbalance, coupling, ground-state data) is unaffected by the swap. -/

/-- The canonically-oriented sublattice: `A` itself if `|¬A| ≤ |A|` already, otherwise its
complement. Matches Theorem 2.3's `horient` hypothesis by construction. -/
noncomputable def liebOrientedSublattice (A : Finset (Fin (N + 1))) :
    Finset (Fin (N + 1)) :=
  if (bipartitionComplement A).card ≤ A.card then A else bipartitionComplement A

/-- The oriented sublattice satisfies Theorem 2.3's orientation hypothesis `|¬A'| ≤ |A'|`. -/
theorem liebOrientedSublattice_horient (A : Finset (Fin (N + 1))) :
    (bipartitionComplement (liebOrientedSublattice A)).card ≤
      (liebOrientedSublattice A).card := by
  sorry

/-- Swapping to the oriented sublattice preserves nondegeneracy: if both `A` and its complement are
nonempty, so are the oriented sublattice and its complement. -/
theorem liebOrientedSublattice_card_pos (A : Finset (Fin (N + 1)))
    (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card) :
    1 ≤ (liebOrientedSublattice A).card ∧
      1 ≤ (bipartitionComplement (liebOrientedSublattice A)).card := by
  sorry

/-- The oriented sublattice has the same sublattice imbalance as `A`: `sublatticeImbalance` is
`Int.natAbs`-based, hence symmetric under the simultaneous `A ↔ Aᶜ` swap. -/
theorem liebOrientedSublattice_sublatticeImbalance_eq (A : Finset (Fin (N + 1))) :
    sublatticeImbalance (liebOrientedSublattice A) = sublatticeImbalance A := by
  sorry

/-- The bipartite coupling built from the oriented sublattice agrees entrywise with the one built
from `A` directly: `bipartiteCoupling` only detects whether the two indicators *differ*, which is
unchanged by flipping both sides of the bipartition simultaneously. -/
theorem liebOrientedSublattice_bipartiteCoupling_eq (A : Finset (Fin (N + 1))) :
    bipartiteCoupling (fun x => decide (x ∈ liebOrientedSublattice A))
      = bipartiteCoupling (fun x : Fin (N + 1) => decide (x ∈ A)) := by
  sorry

/-! ## `J`-hypotheses for `J = (2 : ℂ) • bipartiteCoupling A'` (including the `hJ_pos` bridge)

These discharge the six `J`-shape hypotheses of `tasaki_2_5_theorem_2_3`
(`Theorem23StructuralBipartiteToy.lean:40`) at the concrete coupling PR-9a's capstone produces. -/

/-- `J = (2 : ℂ) • bipartiteCoupling A'` has no imaginary part (`hJ_real`). -/
theorem liebRepulsiveJ_hJ_real (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1)) :
    (((2 : ℂ) • bipartiteCoupling A') x y).im = 0 := by
  sorry

/-- `J = (2 : ℂ) • bipartiteCoupling A'` is Hermitian entrywise (`hJ_real'`; follows from realness).
-/
theorem liebRepulsiveJ_hJ_real' (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1)) :
    star (((2 : ℂ) • bipartiteCoupling A') x y) = ((2 : ℂ) • bipartiteCoupling A') x y := by
  sorry

/-- `J = (2 : ℂ) • bipartiteCoupling A'` is symmetric (`hJ_sym`). -/
theorem liebRepulsiveJ_hJ_sym (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1)) :
    ((2 : ℂ) • bipartiteCoupling A') x y = ((2 : ℂ) • bipartiteCoupling A') y x := by
  sorry

/-- `J = (2 : ℂ) • bipartiteCoupling A'` has nonnegative real part everywhere (`hJ_nn`). -/
theorem liebRepulsiveJ_hJ_nn (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1)) :
    0 ≤ (((2 : ℂ) • bipartiteCoupling A') x y).re := by
  sorry

/-- `J = (2 : ℂ) • bipartiteCoupling A'` vanishes on same-sublattice pairs (`hJ_bipartite`). -/
theorem liebRepulsiveJ_hJ_bipartite (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1))
    (h : A' x = A' y) :
    ((2 : ℂ) • bipartiteCoupling A') x y = 0 := by
  sorry

/-- **The `hJ_pos` bridge**: `J = (2 : ℂ) • bipartiteCoupling A'` is strictly positive on every
edge of `bipartiteCompleteGraphOf A'` — `bipartiteCoupling A'` and `bipartiteCompleteGraphOf A'`
agree entry for entry on adjacency (design note: "agree entry for entry at the same indicator"). -/
theorem liebRepulsiveJ_hJ_pos (A' : Fin (N + 1) → Bool) (x y : Fin (N + 1))
    (hadj : (bipartiteCompleteGraphOf A').Adj x y) :
    0 < (((2 : ℂ) • bipartiteCoupling A') x y).re := by
  sorry

/-! ## Strict diagonal bound witnesses (`hc_strict`, `hc_strict_toy`)

Per the design note, these bounds are to be supplied as explicit constants (e.g. above the finite
max of the dressed diagonal over the finite configuration space), not carried as extra hypotheses
of the capstone. -/

/-- A strict diagonal upper bound exists for the dressed sector matrix of
`J = (2 : ℂ) • bipartiteCoupling A'` (`hc_strict`). -/
theorem exists_liebRepulsiveJ_hc_strict (A' : Fin (N + 1) → Bool) :
    ∃ c : ℝ, ∀ σ, dressedHeisenbergSReMatrix A' ((2 : ℂ) • bipartiteCoupling A') N σ σ < c := by
  sorry

/-- A strict diagonal upper bound exists for the toy dressed sector matrix (`hc_strict_toy`, the
side-condition of `tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`). -/
theorem exists_liebRepulsiveJ_hc_strict_toy (A' : Fin (N + 1) → Bool) :
    ∃ c_toy : ℝ, ∀ σ, dressedHeisenbergSReMatrix A' (bipartiteCoupling A') N σ σ < c_toy := by
  sorry

/-! ## The Theorem 2.3 instance capstone -/

/-- **PR-10b target (scaffold)**: `tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`
instantiated at `J = (2 : ℂ) • bipartiteCoupling A'`, `N_spin = 1`, on the oriented sublattice, for
a nondegenerate bipartition. Unfolds to: for every admissible sector `M`, a Marshall-positive ground
state of `heisenbergHamiltonianSMatrixOnMagSector` at the common ground energy `μ`, together with
the per-sector uniqueness clause and the global energy-minimality clause of
`tasaki_2_5_theorem_2_3`.

`A = ∅` / `A = Finset.univ` are excluded by `hA`/`hB` (see module scope note); those endpoints are
handled directly in a later PR of the arc. -/
theorem liebRepulsive_theorem23_instance (A : Finset (Fin (N + 1)))
    (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card) :
    tasaki_2_5_theorem_2_3
      (fun x => decide (x ∈ liebOrientedSublattice A))
      1
      ((2 : ℂ) • bipartiteCoupling (fun x => decide (x ∈ liebOrientedSublattice A)))
      (Classical.choose
        (exists_liebRepulsiveJ_hc_strict (fun x => decide (x ∈ liebOrientedSublattice A)))) := by
  sorry

/-! ## Casimir transport (PR-9b bridge composition)

Ties `liebRepulsive_theorem23_instance`'s Marshall-positive ground state Casimir eigenvalue
(via `tasaki23_pf_groundState_casimir_eq_predicted_sector`) to the fermionic `Ŝ²` eigenvalue on the
hard-core half-filling sector (via PR-9b's
`fermionTotalSpinSquared_reindex_eq_totalSpinSSquaredOnMagSector`), and identifies the predicted
value with Theorem 10.4's target `liebRepulsiveSpinCasimir A`. -/

/-- `tasaki23PredictedCasimirValue` at `N_spin = 1` on the oriented sublattice equals Theorem
10.4's target Casimir `liebRepulsiveSpinCasimir A` (both reduce to `(sublatticeImbalance A / 2) *
(sublatticeImbalance A / 2 + 1)`, using `tasaki23PredictedTotalSpin_eq_sector_half_width` and
`liebOrientedSublattice_sublatticeImbalance_eq`). -/
theorem liebRepulsiveSpinCasimir_eq_tasaki23PredictedCasimirValue (A : Finset (Fin (N + 1))) :
    liebRepulsiveSpinCasimir A =
      (tasaki23PredictedCasimirValue (V := Fin (N + 1))
        (fun x => decide (x ∈ liebOrientedSublattice A)) 1 : ℝ) := by
  sorry

/-- **PR-10b Casimir-transport capstone (scaffold)**: for a nondegenerate bipartition and an
admissible magnetization sector `nUp` (`N + 1 - nUp` an admissible sector of the oriented
sublattice, per `tasaki23GroundStateSectors_mem_iff`), the fermionic hard-core half-filling sector
carries a nonzero vector on which `fermionTotalSpinSquared N` acts as `liebRepulsiveSpinCasimir A`.

Composes `liebRepulsive_theorem23_instance`'s Marshall-positive eigenvector,
`tasaki23_pf_groundState_casimir_eq_predicted_sector`'s Casimir identification, PR-9a's Hamiltonian
reindexing, and PR-9b's Casimir reindexing
(`fermionTotalSpinSquared_reindex_eq_totalSpinSSquaredOnMagSector`). The sector-bridge work
connecting this hard-core-sector statement to Theorem 10.4's `hubbardGroundSubmoduleAtElectronNumber`
target is PR-11's responsibility, not this lemma's. -/
theorem liebRepulsive_groundState_casimir_eq_predicted (A : Finset (Fin (N + 1)))
    (hA : 1 ≤ A.card) (hB : 1 ≤ (bipartitionComplement A).card)
    (nUp : ℕ) (hnUp : nUp ≤ N + 1)
    (hM : (N + 1 - nUp) ∈ tasaki23GroundStateSectors
      (fun x => decide (x ∈ liebOrientedSublattice A)) 1) :
    ∃ c : configSector N (liebHardCoreHalfFillingPred N nUp) → ℂ, c ≠ 0 ∧
      ((fermionTotalSpinSquared N).submatrix
          (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)
          (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)).mulVec c
        = liebRepulsiveSpinCasimir A • c := by
  sorry

end LatticeSystem.Fermion
