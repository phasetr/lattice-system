import LatticeSystem.Fermion.JordanWigner.Hubbard.AllUpState
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJCrossSiteSpinCommute

/-!
# Tasaki 11.5.3: the spin dot product on the all-up state (Theorem 11.26 PR3a)

The all-up state `|↑…↑⟩` is the maximal-spin reference for the half-filling ferromagnetic
Heisenberg model.  On it the per-site raising operator vanishes, the per-site `Ŝ^z` acts as `½`,
and for `i ≠ j` the two-site dot product is the aligned value `¼`:

* `fermionSiteSpinPlus_mulVec_allUpState` — `Ŝ⁺_i |↑…↑⟩ = 0`;
* `fermionSiteSpinZ_mulVec_allUpState` — `Ŝ³_i |↑…↑⟩ = ½ |↑…↑⟩`;
* `fermionSpinDot_mulVec_allUpState` — `Ŝ_i·Ŝ_j |↑…↑⟩ = ¼ |↑…↑⟩` for `i ≠ j`.

The off-diagonal `Ŝ⁺_i Ŝ⁻_j` and `Ŝ⁻_i Ŝ⁺_j` both annihilate `|↑…↑⟩`: the latter directly via
`Ŝ⁺_j |↑…↑⟩ = 0`, the former because `ĉ_{i↓}` commutes through the different-site `Ŝ⁻_j` to hit
`|↑…↑⟩` (which has no down electron).  Only the diagonal `Ŝ³_i Ŝ³_j = ¼` survives.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- `Ŝ⁺_i |↑…↑⟩ = 0`: the raising operator needs a down electron, but `|↑…↑⟩` has none. -/
theorem fermionSiteSpinPlus_mulVec_allUpState (N : ℕ) (i : Fin (N + 1)) :
    (fermionSiteSpinPlus N i).mulVec (hubbardAllUpState N) = 0 := by
  rw [fermionSiteSpinPlus, ← Matrix.mulVec_mulVec, fermionDownAnnihilation_mulVec_allUpState,
    Matrix.mulVec_zero]

/-- `Ŝ³_i |↑…↑⟩ = ½ |↑…↑⟩`: site `i` carries one up electron (`n_{i↑}=1`, `n_{i↓}=0`). -/
theorem fermionSiteSpinZ_mulVec_allUpState (N : ℕ) (i : Fin (N + 1)) :
    (fermionSiteSpinZ N i).mulVec (hubbardAllUpState N) = (1 / 2 : ℂ) • hubbardAllUpState N := by
  rw [fermionSiteSpinZ, Matrix.smul_mulVec, Matrix.sub_mulVec,
    show fermionUpCreation N i * fermionUpAnnihilation N i = fermionUpNumber N i from rfl,
    show fermionDownCreation N i * fermionDownAnnihilation N i = fermionDownNumber N i from rfl,
    fermionUpNumber_mulVec_allUpState, fermionDownNumber_mulVec_allUpState, sub_zero]

/-- **The spin dot product on the all-up state.**  For `i ≠ j`, `Ŝ_i·Ŝ_j |↑…↑⟩ = ¼ |↑…↑⟩`: the
raising/lowering terms annihilate `|↑…↑⟩`, leaving `Ŝ³_i Ŝ³_j = ¼`. -/
theorem fermionSpinDot_mulVec_allUpState (N : ℕ) (i j : Fin (N + 1)) (hij : i ≠ j) :
    (fermionSpinDot N i j).mulVec (hubbardAllUpState N) = (1 / 4 : ℂ) • hubbardAllUpState N := by
  have hSmSp : (fermionSiteSpinMinus N i * fermionSiteSpinPlus N j).mulVec
      (hubbardAllUpState N) = 0 := by
    rw [← Matrix.mulVec_mulVec, fermionSiteSpinPlus_mulVec_allUpState, Matrix.mulVec_zero]
  have hSpSm : (fermionSiteSpinPlus N i * fermionSiteSpinMinus N j).mulVec
      (hubbardAllUpState N) = 0 := by
    rw [fermionSiteSpinPlus, mul_assoc,
      (fermionDownAnnihilation_commute_fermionSiteSpinMinus_of_ne i j hij).eq, ← mul_assoc,
      ← Matrix.mulVec_mulVec, fermionDownAnnihilation_mulVec_allUpState, Matrix.mulVec_zero]
  have hSzSz : (fermionSiteSpinZ N i * fermionSiteSpinZ N j).mulVec (hubbardAllUpState N) =
      (1 / 4 : ℂ) • hubbardAllUpState N := by
    rw [← Matrix.mulVec_mulVec, fermionSiteSpinZ_mulVec_allUpState, Matrix.mulVec_smul,
      fermionSiteSpinZ_mulVec_allUpState, smul_smul]
    norm_num
  rw [fermionSpinDot, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, hSpSm, hSmSp,
    add_zero, smul_zero, zero_add, hSzSz]

end LatticeSystem.Fermion
