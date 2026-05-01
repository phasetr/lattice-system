import LatticeSystem.Quantum.MarshallLiebMattis.HeisenbergSwapEntry

/-!
# Test coverage for off-bond non-equality
-/

namespace LatticeSystem.Tests.MarshallLiebMattisHeisenbergSwapEntry

open LatticeSystem.Quantum

/-- Off-bond non-equality on `Fin 3`: for the bond `(0, 1)` vs the
test bond `(0, 2)`, swapping at `(0, 2)` of the swapped configuration
does not return to σ. -/
example {σ : Fin 3 → Fin 2} (h : σ 0 ≠ σ 1) :
    basisSwap (basisSwap σ 0 1) 0 2 ≠ σ := by
  apply basisSwap_basisSwap_ne_self_of_ne_bond (by decide : (0 : Fin 3) ≠ 1) h
  rintro (⟨_, hv⟩ | ⟨hu, _⟩)
  · exact (by decide : (2 : Fin 3) ≠ 1) hv
  · exact (by decide : (0 : Fin 3) ≠ 1) hu

end LatticeSystem.Tests.MarshallLiebMattisHeisenbergSwapEntry
