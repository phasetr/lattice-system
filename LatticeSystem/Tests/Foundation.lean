/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Lattice.Graph
import LatticeSystem.Quantum.HeisenbergChain
import LatticeSystem.Quantum.NeelState

/-!
# Test foundation POC (refactor Phase 0, #280)

This file demonstrates each test method adopted in the refactoring
plan v4 (`.self-local/docs/refactoring-plan-2026-04-22.md` §2.1).
The intent is to confirm each idiom builds in mathlib v4.29.0 + Lean 4
before applying it across the codebase in Phase 1.

Methods covered:
- A. decide-based universal property test (finite Decidable predicates).
- B. matrix entry-wise on small `Fin n` (`ext i j <;> fin_cases`).
- C. bridge identity (definitional equality between two definitions).
- F. `#guard_msgs` (deprecation warning capture).
- G. small exhaustive (`Fin n; fin_cases`) (semantic verification on
  small instances).

`D` (signature shim) is already standard across existing test files;
no separate POC needed.
`E` (`Plausible`) is intentionally deferred — generator integration
cost is high for our `ℂ` / matrix setting.
-/

namespace LatticeSystem.Tests.Foundation

open LatticeSystem.Quantum LatticeSystem.Lattice

/-! ## A. decide-based universal property test

Demonstrates that finite, `Decidable` propositions can be discharged
by `decide`. This is the most refactor-resistant test category: it
depends on the *meaning* of the predicate, not on any theorem name. -/

/-- `pathGraph` adjacency on `Fin 4` is symmetric (universally
verified by `decide`). -/
example :
    ∀ x y : Fin 4, (SimpleGraph.pathGraph 4).Adj x y =
      (SimpleGraph.pathGraph 4).Adj y x := by decide

/-- `pathGraph` adjacency on `Fin 4` is irreflexive (universal). -/
example :
    ∀ x : Fin 4, ¬ (SimpleGraph.pathGraph 4).Adj x x := by decide

/-- Néel parity colouring on `Fin 4` alternates (universal). -/
example :
    ∀ i : Fin 4,
        (neelChainConfig 2 i = (0 : Fin 2)) ↔ (i.val % 2 = 0) := by
  decide

/-! ## B. matrix entry-wise on small `Fin n`

Demonstrates that small matrix-valued definitions can be pinned to
explicit `!![..]` literals via `ext + fin_cases`. Concrete numerical
values catch any meaning change immediately. -/

/-- `openChainCoupling 1 J` evaluated entry-wise:
`!![0, -J; -J, 0]`. -/
example (J : ℝ) :
    openChainCoupling 1 J = !![0, -(J : ℂ); -(J : ℂ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [openChainCoupling_apply]

/-! ## C. bridge identity

Demonstrates the definitional equality between two ways of expressing
the same object. Refactor-resistant in the sense that *both* sides
breaking would pinpoint the divergence. -/

/-- `openChainCoupling N J = couplingOf (pathGraph (N + 1)) (-J)`
holds definitionally. -/
example (N : ℕ) (J : ℝ) :
    openChainCoupling N J =
      couplingOf (SimpleGraph.pathGraph (N + 1)) (-(J : ℂ)) := rfl

/-- `periodicChainCoupling N J = couplingOf (cycleGraph (N + 2)) (-J)`
holds definitionally. -/
example (N : ℕ) (J : ℝ) :
    periodicChainCoupling N J =
      couplingOf (SimpleGraph.cycleGraph (N + 2)) (-(J : ℂ)) := rfl

/-! ## F. `#guard_msgs` for deprecation warning capture

Demonstrates that `#guard_msgs` can be used to pin the diagnostic
output of a command. Intended use cases:
- `@[deprecated]` warning text.
- Intended `error`-level command output.
- Linter behaviour fixation.

This POC defines a small deprecated symbol and verifies the
expected warning message is emitted. -/

/-- A throw-away deprecated `def` for the `#guard_msgs` POC. -/
@[deprecated "POC: use `foundationPocReplacement`" (since := "2026-04-22")]
def foundationPocOldDef : ℕ := 0

/-- The intended replacement (also throw-away). -/
def foundationPocReplacement : ℕ := 0

/--
warning: `LatticeSystem.Tests.Foundation.foundationPocOldDef` has been deprecated: POC: use `foundationPocReplacement`
-/
#guard_msgs in
example : ℕ := foundationPocOldDef

/-! ## G. small exhaustive (`Fin n; fin_cases`)

Demonstrates exhaustive verification on a small instance: enumerate
all relevant indices via `fin_cases` and discharge each by `simp` /
`decide` / `rfl`. This is the most refactor-resistant test for
parameterised lemmas: it pins the *meaning* on a small but complete
sample of the parameter space.

Used here to verify that the Néel chain at `K = 2` is antiparallel
on every adjacent bond. -/

/-- For every adjacent bond `(i, i + 1)` of `Fin 4 = Fin (2 * 2)`,
the Néel chain configuration is antiparallel. Exhaustive over `i`. -/
example :
    ∀ i : Fin 3,
        neelChainConfig 2 (⟨i.val, by omega⟩ : Fin 4) ≠
          neelChainConfig 2 (⟨i.val + 1, by omega⟩ : Fin 4) := by
  decide

/-- Néel chain configuration on `Fin 4`, computed entry-wise. -/
example : neelChainConfig 2 (⟨0, by decide⟩ : Fin 4) = 0 := by decide
example : neelChainConfig 2 (⟨1, by decide⟩ : Fin 4) = 1 := by decide
example : neelChainConfig 2 (⟨2, by decide⟩ : Fin 4) = 0 := by decide
example : neelChainConfig 2 (⟨3, by decide⟩ : Fin 4) = 1 := by decide

end LatticeSystem.Tests.Foundation
