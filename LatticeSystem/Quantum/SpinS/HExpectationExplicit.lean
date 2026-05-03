import LatticeSystem.Quantum.SpinS.SaturatedHeisenbergExpectation
import LatticeSystem.Quantum.SpinS.SaturatedHeisenbergExpectationClean
import LatticeSystem.Quantum.SpinS.SaturatedEigenvalueExplicit

/-!
# Heisenberg expectation on saturated states: explicit form

Combines PR #943 / #948 with PR #951 to give the explicit
combinatorial form of the H expectation:

  `⟨|σ_⊤⟩, H · |σ_⊤⟩⟩ =
   ∑_x ∑_y J(x, y) · (if x = y then N(N+2)/4 else (N/2)²)`

(and symmetric for `|σ_⊥⟩`).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- Explicit form of `⟨|σ_⊤⟩, H · |σ_⊤⟩⟩`. -/
theorem allAlignedStateS_zero_expectation_heisenbergHamiltonianS_explicit
    (J : V → V → ℂ) :
    dotProduct (star (allAlignedStateS V N (0 : Fin (N + 1))))
      ((heisenbergHamiltonianS J N).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2)) := by
  rw [allAlignedStateS_zero_expectation_heisenbergHamiltonianS]
  exact saturatedFerromagnetEigenvalueS_explicit J

/-- Symmetric explicit form of `⟨|σ_⊥⟩, H · |σ_⊥⟩⟩`. -/
theorem allAlignedStateS_last_expectation_heisenbergHamiltonianS_explicit
    (J : V → V → ℂ) :
    dotProduct (star (allAlignedStateS V N (Fin.last N)))
      ((heisenbergHamiltonianS J N).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      ∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2)) := by
  rw [allAlignedStateS_last_expectation_heisenbergHamiltonianS_eq_saturated]
  exact saturatedFerromagnetEigenvalueS_explicit J

end LatticeSystem.Quantum
