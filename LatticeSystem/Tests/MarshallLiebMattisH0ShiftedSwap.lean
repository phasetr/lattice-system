import LatticeSystem.Quantum.MarshallLiebMattis.H0ShiftedSwap

/-!
# Test coverage for B strict positivity on swap-related H_0 configurations
-/

namespace LatticeSystem.Tests.MarshallLiebMattisH0ShiftedSwap

open LatticeSystem.Quantum

/-- B σ τ > 0 on swap-related H_0 configurations with positive J. -/
example (A : Fin 2 → Bool) {J : Fin 2 → Fin 2 → ℂ}
    (hJ_symm : ∀ x y, J x y = J y x) (hA : A 0 ≠ A 1)
    (hJ01_pos : 0 < (J 0 1).re) (c : ℝ)
    {σ : H₀Index (Fin 2)} (h : σ.val 0 ≠ σ.val 1)
    (τ : H₀Index (Fin 2)) (hτ : τ.val = basisSwap σ.val 0 1) :
    0 < dressedHeisenbergShifted A J c σ τ :=
  dressedHeisenbergShifted_pos_of_basisSwap A hJ_symm
    (by decide : (0 : Fin 2) ≠ 1) hA hJ01_pos c h τ hτ

end LatticeSystem.Tests.MarshallLiebMattisH0ShiftedSwap
