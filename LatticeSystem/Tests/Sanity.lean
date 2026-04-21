/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Quantum.SpinHalfBasis
import LatticeSystem.Lattice.Graph
import LatticeSystem.Quantum.HeisenbergChain

/-!
# Sanity / regression test suite

In Lean 4 the proofs verify all properties for all inputs, so there
is no traditional "test suite" separate from the source. This file
nevertheless collects explicit `example` blocks that pin down
concrete-instance values for the existing infrastructure.

The intent is twofold:
1. **Regression guard**: any future refactor that changes the
   meaning of a definition will break these `example` blocks
   loudly.
2. **Cross-check**: the example values can be hand-computed and
   compared against authoritative references (Tasaki, etc.).

Property tests in the QuickCheck sense (random sampling over a
type) are not part of mathlib's idiom; the proofs themselves
provide the universal guarantee. The `example` blocks here are
analogous to "concrete unit tests" exercising small inputs.
-/

namespace LatticeSystem.Tests

open LatticeSystem.Quantum LatticeSystem.Lattice Matrix Complex

/-! ## Pauli matrix arithmetic

Standard Pauli identities at small concrete inputs. -/

/-- σ^x is its own inverse. -/
example : pauliX * pauliX = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  pauliX_mul_self

/-- σ^z is its own inverse. -/
example : pauliZ * pauliZ = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  pauliZ_mul_self

/-- σ^x and σ^z anticommute: `σ^x σ^z + σ^z σ^x = 0`. -/
example :
    pauliX * pauliZ + pauliZ * pauliX = (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliZ]

/-! ## Single-site spin-1/2 ladder action

Tasaki eq. (2.1.5): `Ŝ^- |↑⟩ = |↓⟩`, `Ŝ^+ |↓⟩ = |↑⟩`. -/

/-- `Ŝ^- |↑⟩ = |↓⟩`. -/
example : spinHalfOpMinus.mulVec spinHalfUp = spinHalfDown :=
  spinHalfOpMinus_mulVec_spinHalfUp

/-- `Ŝ^+ |↓⟩ = |↑⟩`. -/
example : spinHalfOpPlus.mulVec spinHalfDown = spinHalfUp :=
  spinHalfOpPlus_mulVec_spinHalfDown

/-! ## Graph-centric coupling sanity

`couplingOf G J` should match the explicit chain-coupling formulas
on small chains. -/

/-- `pathGraph 2` adjacency: only `0 ~ 1` and `1 ~ 0` are edges. -/
example : (SimpleGraph.pathGraph 2).Adj (0 : Fin 2) 1 := by
  rw [pathGraph_adj_iff]; left; rfl

/-- The `0–0` self-loop is excluded. -/
example : ¬ (SimpleGraph.pathGraph 2).Adj (0 : Fin 2) 0 :=
  (SimpleGraph.pathGraph 2).irrefl

/-- `couplingOf G J` is zero on the diagonal. -/
example (J : ℂ) : couplingOf (SimpleGraph.pathGraph 2) J 0 0 = 0 :=
  couplingOf_self _ J _

/-- `couplingOf G J` is symmetric. -/
example (J : ℂ) (x y : Fin 2) :
    couplingOf (SimpleGraph.pathGraph 2) J x y =
      couplingOf (SimpleGraph.pathGraph 2) J y x :=
  couplingOf_symm _ J x y

/-- The 2-site open chain coupling matches `couplingOf (pathGraph 2) (-J)`. -/
example (J : ℝ) :
    openChainCoupling 1 J =
      couplingOf (SimpleGraph.pathGraph 2) (-(J : ℂ)) :=
  openChainCoupling_eq_couplingOf 1 J

/-- The 3-site periodic chain coupling matches
`couplingOf (cycleGraph 3) (-J)`. -/
example (J : ℝ) :
    periodicChainCoupling 1 J =
      couplingOf (SimpleGraph.cycleGraph 3) (-(J : ℂ)) :=
  periodicChainCoupling_eq_couplingOf 1 J

/-! ## Heisenberg chain Hermiticity (concrete N) -/

/-- The 2-site (N = 1) open Heisenberg chain Hamiltonian is Hermitian. -/
example (J : ℝ) :
    (heisenbergHamiltonian (openChainCoupling 1 J)).IsHermitian :=
  openChainHeisenberg_isHermitian 1 J

/-- The 3-site (N = 1, periodic) Heisenberg chain Hamiltonian is Hermitian. -/
example (J : ℝ) :
    (heisenbergHamiltonian (periodicChainCoupling 1 J)).IsHermitian :=
  periodicChainHeisenberg_isHermitian 1 J

/-- Graph-centric Hermiticity (any graph, real edge weight). -/
example (J : ℝ) :
    (heisenbergHamiltonian
        (couplingOf (SimpleGraph.pathGraph 2) (-(J : ℂ)))).IsHermitian :=
  heisenbergHamiltonian_couplingOf_isHermitian _ (by simp)

end LatticeSystem.Tests
