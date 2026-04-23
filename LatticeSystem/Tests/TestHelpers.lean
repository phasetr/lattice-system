/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Lattice.Graph
import LatticeSystem.Quantum.NeelState

/-!
# Test helpers (refactor Phase 1 PR 1, #281)

Common utilities and naming conventions for the Phase 1 test
reinforcement series (P1-2 through P1-14). These helpers are
intentionally minimal: most tests will rely on `decide` /
`fin_cases` / `simp` directly. The helpers exist primarily to:

1. Name and document the common test patterns (A / C / G of the
   refactor plan v4 §2.1).
2. Provide a single import path for reusable test fixtures.

## Method index

- **A. decide-based universal**: `by decide` on a `∀ x : Fin n, ...`
  predicate.
- **B. matrix entry-wise**: `ext i j; fin_cases i <;> fin_cases j <;>
  simp [defn_apply]`.
- **C. bridge identity**: two definitions, equal by `rfl` /
  `unfold + simp`.
- **D. signature shim**: `example : <type> := named_thm args`.
- **F. `#guard_msgs`**: `/-- expected msg -/ #guard_msgs in <command>`.
- **G. small exhaustive**: `Fin 2/3/4` enumerated by `fin_cases`.

See `docs/refactoring-conventions.md` §1
([project page](https://phasetr.github.io/lattice-system/refactoring-conventions/#1-test-methods-per-refactor-plan-v4-§21))
for the full method matrix and review checklist.
-/

namespace LatticeSystem.Tests.Helpers

open LatticeSystem.Quantum LatticeSystem.Lattice

/-! ## A. decide-based universal — convenience aliases

Sample utility predicates intended to be reused by Phase 1 tests.
All are `Decidable` so they can be discharged by `decide`. -/

/-- A `SimpleGraph` adjacency relation is symmetric (universally on
the chosen finite type). Specialised by `decide` on small `Fin n`. -/
def adjSymmetricOn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ x y : V, G.Adj x y = G.Adj y x

/-- A `SimpleGraph` adjacency relation is irreflexive. -/
def adjIrreflexiveOn {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ x : V, ¬ G.Adj x x

/-- The Néel chain configuration alternates strictly between
adjacent indices on `Fin (2 * K)`. -/
def neelChainAdjacentAntiparallel (K : ℕ) : Prop :=
  ∀ i : Fin (2 * K - 1),
      neelChainConfig K (⟨i.val, by omega⟩ : Fin (2 * K)) ≠
        neelChainConfig K (⟨i.val + 1, by omega⟩ : Fin (2 * K))

/-! ## Sanity: helpers compile and `decide` works on small `Fin n` -/

example : adjSymmetricOn (SimpleGraph.pathGraph 4) := by
  unfold adjSymmetricOn; decide

example : adjIrreflexiveOn (SimpleGraph.pathGraph 4) := by
  unfold adjIrreflexiveOn; decide

example : neelChainAdjacentAntiparallel 2 := by
  unfold neelChainAdjacentAntiparallel; decide

end LatticeSystem.Tests.Helpers
