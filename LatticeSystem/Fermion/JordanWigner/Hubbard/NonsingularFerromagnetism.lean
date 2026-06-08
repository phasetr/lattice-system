import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularFrustrationFree
import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularFrustrationFreePos
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandHighestWeight
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral

/-!
# Tasaki §11.4.3 Lemma 11.21: ferromagnetism assembly (Issue #4189)

Assembling the discharge of `nonsingular_lemma_11_21` from the proved pieces:
* `ĥ_p|Φ↑⟩=0` ⟹ `Ĥ|Φ↑⟩ = −C·|Φ↑⟩` (`tasakiNonsingularHamiltonian_mulVec_alphaAllUpState`),
* `Ĥ + C·1 ≥ 0` (`tasakiNonsingular_add_const_posSemidef`),
* the maximal-spin sector membership of `|Φ↑⟩` (here),

towards `exhibitsFerromagnetism` (the maximal-spin sector lies strictly below all others).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.),
§11.4.3, Lemma 11.21 (pp. 429–431).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **`(Ŝ_tot)² |Φα,all↑⟩ = S_max(S_max+1) |Φα,all↑⟩`** with `S_max = (K+1)/2` (twoS = K+1).  The
all-up flat-band state is a highest-weight state (`Ŝ⁺_tot|Φ↑⟩=0`, `Ŝ³_tot|Φ↑⟩=((K+1)/2)|Φ↑⟩`), so
its Casimir value is `m(m+1)` — positivity-free, via
`fermionTotalSpinSquared_mulVec_of_isTop_general`. -/
theorem flatBandTotalSpinSquared_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) :
    (fermionTotalSpinSquared (2 * K + 1)).mulVec (flatBandAlphaAllUpState K ν)
      = (((K + 1 : ℕ) : ℂ) / 2 * (((K + 1 : ℕ) : ℂ) / 2 + 1)) • flatBandAlphaAllUpState K ν :=
  fermionTotalSpinSquared_mulVec_of_isTop_general (2 * K + 1) (flatBandAlphaAllUpState K ν)
    (((K + 1 : ℕ) : ℂ) / 2)
    (flatBandTotalSpinPlus_mulVec_alphaAllUpState K ν)
    (flatBandTotalSpinZ_mulVec_alphaAllUpState K ν)

end LatticeSystem.Fermion
