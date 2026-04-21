/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState

/-!
# Test coverage for the Néel chain state (Tasaki §2.5)
-/

namespace LatticeSystem.Tests.NeelState

open LatticeSystem.Quantum

/-! ## Configuration values at small chain lengths -/

example : neelChainConfig 1 ⟨0, by decide⟩ = (0 : Fin 2) := by
  decide
example : neelChainConfig 1 ⟨1, by decide⟩ = (1 : Fin 2) := by
  decide
example : neelChainConfig 2 ⟨0, by decide⟩ = (0 : Fin 2) := by
  decide
example : neelChainConfig 2 ⟨1, by decide⟩ = (1 : Fin 2) := by
  decide
example : neelChainConfig 2 ⟨2, by decide⟩ = (0 : Fin 2) := by
  decide
example : neelChainConfig 2 ⟨3, by decide⟩ = (1 : Fin 2) := by
  decide

/-! ## Magnetisation = 0 -/

example : magnetization (Fin (2 * 1)) (neelChainConfig 1) = 0 :=
  neelChainConfig_magnetization_zero 1
example : magnetization (Fin (2 * 2)) (neelChainConfig 2) = 0 :=
  neelChainConfig_magnetization_zero 2
example : magnetization (Fin (2 * 3)) (neelChainConfig 3) = 0 :=
  neelChainConfig_magnetization_zero 3

/-! ## Membership in the zero-magnetisation sector `H_0` -/

example : neelChainState 1 ∈ magnetizationSubspace (Fin (2 * 1)) (0 : ℂ) :=
  neelChainState_mem_magnetizationSubspace_zero 1
example : neelChainState 2 ∈ magnetizationSubspace (Fin (2 * 2)) (0 : ℂ) :=
  neelChainState_mem_magnetizationSubspace_zero 2
example : neelChainState 3 ∈ magnetizationSubspace (Fin (2 * 3)) (0 : ℂ) :=
  neelChainState_mem_magnetizationSubspace_zero 3

/-! ## H · |Φ_Néel⟩ stays in `H_0` (SU(2) invariance corollary) -/

example (K : ℕ) (J : Fin (2 * K) → Fin (2 * K) → ℂ) :
    (heisenbergHamiltonian J).mulVec (neelChainState K) ∈
      magnetizationSubspace (Fin (2 * K)) (0 : ℂ) :=
  heisenbergHamiltonian_mulVec_neelChainState_mem_magnetizationSubspace_zero K J

example (J : Fin (2 * 2) → Fin (2 * 2) → ℂ) :
    (heisenbergHamiltonian J).mulVec (neelChainState 2) ∈
      magnetizationSubspace (Fin (2 * 2)) (0 : ℂ) :=
  heisenbergHamiltonian_mulVec_neelChainState_mem_magnetizationSubspace_zero 2 J

end LatticeSystem.Tests.NeelState
