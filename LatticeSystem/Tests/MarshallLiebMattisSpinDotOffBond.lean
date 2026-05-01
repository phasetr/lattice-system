/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallLiebMattis.SpinDotOffBond

/-!
# Test coverage for off-bond spinHalfDot vanishing
-/

namespace LatticeSystem.Tests.MarshallLiebMattisSpinDotOffBond

open LatticeSystem.Quantum

/-- For an off-bond pair `(0, 2)` (vs the swap bond `(0, 1)`):
the spinHalfDot matrix entry vanishes. -/
example {σ : Fin 3 → Fin 2} (h : σ 0 ≠ σ 1) :
    (spinHalfDot (0 : Fin 3) 2) σ (basisSwap σ 0 1) = 0 := by
  apply spinHalfDot_apply_basisSwap_off_bond_eq_zero
    (by decide : (0 : Fin 3) ≠ 1) h
  rintro (⟨_, hv⟩ | ⟨hu, _⟩)
  · exact (by decide : (2 : Fin 3) ≠ 1) hv
  · exact (by decide : (0 : Fin 3) ≠ 1) hu

end LatticeSystem.Tests.MarshallLiebMattisSpinDotOffBond
