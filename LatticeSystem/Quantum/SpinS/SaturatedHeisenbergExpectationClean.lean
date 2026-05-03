import LatticeSystem.Quantum.SpinS.SaturatedHeisenbergExpectation
import LatticeSystem.Quantum.SpinS.SaturatedHeisenbergSymmetric

/-!
# Symmetric Heisenberg expectation: `|σ_⊥⟩` form via `c_J`

Combines PR #943's `|σ_⊥⟩` Heisenberg expectation
(returning `H(σ_⊥, σ_⊥)`) with PR #946's diagonal symmetry
(`H(σ_⊥, σ_⊥) = saturatedFerromagnetEigenvalueS J N`) to give the
clean form

  `⟨|σ_⊥⟩, H · |σ_⊥⟩⟩ = saturatedFerromagnetEigenvalueS J N`,

matching the `|σ_⊤⟩` statement of PR #943.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `⟨|σ_⊥⟩, H · |σ_⊥⟩⟩ = saturatedFerromagnetEigenvalueS J N`. -/
theorem allAlignedStateS_last_expectation_heisenbergHamiltonianS_eq_saturated
    (J : V → V → ℂ) :
    dotProduct (star (allAlignedStateS V N (Fin.last N)))
      ((heisenbergHamiltonianS J N).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      saturatedFerromagnetEigenvalueS (V := V) J N := by
  rw [allAlignedStateS_last_expectation_heisenbergHamiltonianS]
  exact heisenbergHamiltonianS_diag_allAlignedConfigS_last_eq_zero J

end LatticeSystem.Quantum
