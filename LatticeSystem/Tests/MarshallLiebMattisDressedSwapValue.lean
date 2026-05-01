/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.DressedSwapValue

/-!
# Test coverage for dressed Heisenberg matrix entry value on swap configs
-/

namespace LatticeSystem.Tests.MarshallLiebMattisDressedSwapValue

open LatticeSystem.Quantum

/-- The complex-level dressed pairing value formula. -/
example (A : Fin 2 → Bool) {J : Fin 2 → Fin 2 → ℂ}
    (hJ_symm : ∀ x y, J x y = J y x) (hA : A 0 ≠ A 1)
    {σ : Fin 2 → Fin 2} (h : σ 0 ≠ σ 1) :
    marshallSignOf A σ * marshallSignOf A (basisSwap σ 0 1) *
        (heisenbergHamiltonian J) σ (basisSwap σ 0 1) = -(J 0 1) :=
  dressed_pairing_basisSwap_eq A hJ_symm
    (by decide : (0 : Fin 2) ≠ 1) hA h

/-- Real-part dressed matrix entry on swap-related H_0 configs. -/
example (A : Fin 2 → Bool) {J : Fin 2 → Fin 2 → ℂ}
    (hJ_symm : ∀ x y, J x y = J y x) (hA : A 0 ≠ A 1)
    {σ : H₀Index (Fin 2)} (h : σ.val 0 ≠ σ.val 1)
    (τ : H₀Index (Fin 2)) (hτ : τ.val = basisSwap σ.val 0 1) :
    dressedHeisenbergMatrixH0 A J σ τ = -((J 0 1).re) :=
  dressedHeisenbergMatrixH0_apply_basisSwap A hJ_symm
    (by decide : (0 : Fin 2) ≠ 1) hA h τ hτ

end LatticeSystem.Tests.MarshallLiebMattisDressedSwapValue
