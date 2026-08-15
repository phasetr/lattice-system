import LatticeSystem.Quantum.MarshallLiebMattis.EqMagnetizationReachable

/-!
# Test coverage for equal-magnetisation reachability
(Tasaki §2.5 p. 42 Proposition)
-/

namespace LatticeSystem.Tests.MarshallLiebMattisEqMagnetizationReachable

open LatticeSystem.Quantum

/-- Magnetisation in terms of the spin-`S` magnetisation sum at `N = 1`. -/
example (σ : Fin 2 → Fin 2) :
    magnetization (Fin 2) σ = (Fintype.card (Fin 2) : ℤ) - 2 * (magSumS (N := 1) σ : ℤ) :=
  magnetization_eq_card_sub_two_mul σ

/-- Equal magnetisation is the same hypothesis as an equal magnetisation sum. -/
example (σ σ' : Fin 2 → Fin 2) :
    magnetization (Fin 2) σ = magnetization (Fin 2) σ' ↔
      magSumS (N := 1) σ = magSumS (N := 1) σ' :=
  magnetization_eq_iff_magSumS_eq σ σ'

/-- A spin-`S` raise/lower step at `N = 1` is a bond swap. -/
example (G : SimpleGraph (Fin 2)) {σ σ' : Fin 2 → Fin 2}
    (h : RaiseLowerStepS (N := 1) G σ σ') :
    SwapStep G σ σ' :=
  swapStep_of_raiseLowerStepS h

/-- Tasaki §2.5 p. 42 Proposition: equal-magnetisation reachability. -/
example (G : SimpleGraph (Fin 2)) (hG : G.Preconnected)
    (σ σ' : Fin 2 → Fin 2)
    (hmag : magnetization (Fin 2) σ = magnetization (Fin 2) σ') :
    SwapReachable G σ σ' :=
  swapReachable_of_eq_magnetization hG σ σ' hmag

end LatticeSystem.Tests.MarshallLiebMattisEqMagnetizationReachable
