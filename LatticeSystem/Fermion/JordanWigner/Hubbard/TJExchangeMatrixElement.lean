import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorExchange

/-!
# Tasaki 11.5: the exchange matrix element on the sector basis (Prop 11.24 PR-B5)

The off-diagonal ladder matrix element `⟨Φ_{s'} | Ŝ⁺_i Ŝ⁻_j | Φ_s⟩` for an antiparallel pair
(`s i = ↓`, `s j = ↑`, `i ≠ j`) equals `1` exactly when `s'` is the spin-swapped site-state
`tJSpinSwap s i j`, and `0` otherwise.  This combines the sign-free exchange action
(`fermionSiteSpinPlus_mul_Minus_mulVec_tJConfigOf`) with the orthonormality of the sector basis; it
gives the `−J/2` off-diagonal exchange entry of the t-J effective matrix.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **Exchange spin-flip matrix element.**  For `s i = ↓`, `s j = ↑` (`i ≠ j`),
`⟨Φ_{s'} | Ŝ⁺_i Ŝ⁻_j | Φ_s⟩ = [s' = tJSpinSwap s i j]`. -/
theorem fermionSpinFlip_matrixElement (N : ℕ) (s s' : Fin (N + 1) → Fin 3) (i j : Fin (N + 1))
    (hi : s i = 2) (hj : s j = 1) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionSiteSpinPlus N i * fermionSiteSpinMinus N j).mulVec
            (basisVec (tJConfigOf N s))) w)
      = if s' = tJSpinSwap s i j then 1 else 0 := by
  rw [fermionSiteSpinPlus_mul_Minus_mulVec_tJConfigOf N s i j hi hj]
  exact tJConfigOf_basisVec_inner N s' (tJSpinSwap s i j)

end LatticeSystem.Fermion
