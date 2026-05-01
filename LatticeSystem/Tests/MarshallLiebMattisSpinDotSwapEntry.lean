/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.SpinDotSwapEntry

/-!
# Test coverage for spin-dot swap matrix entry
-/

namespace LatticeSystem.Tests.MarshallLiebMattisSpinDotSwapEntry

open LatticeSystem.Quantum

/-- Off-diagonal matrix entry of `Ŝ_x · Ŝ_y` at swap configurations equals 1/2. -/
example {σ : Fin 2 → Fin 2} (h : σ 0 ≠ σ 1) :
    (spinHalfDot (0 : Fin 2) 1) σ (basisSwap σ 0 1) = (1 / 2 : ℂ) :=
  spinHalfDot_apply_basisSwap (by decide : (0 : Fin 2) ≠ 1) h

end LatticeSystem.Tests.MarshallLiebMattisSpinDotSwapEntry
