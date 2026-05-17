import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelHeisenbergExpectation

/-!
# `⟨Φ_↑⟩.re = ⟨Φ_↓⟩.re` unconditionally

The all-up and all-down state expectations of the toy Heisenberg
Hamiltonian coincide:

  `⟨Φ_↑|Ĥ_toy|Φ_↑⟩.re = ⟨Φ_↓|Ĥ_toy|Φ_↓⟩.re = +|A|·|¬A|·N²/2`

unconditionally. The toy Hamiltonian is invariant under the global
spin flip `m → N − m`, so the two saturated states have identical
expectation values.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **`⟨Φ_↑⟩.re = ⟨Φ_↓⟩.re`** unconditionally: the two saturated
states have identical toy-Hamiltonian expectations. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_last_expectation_re
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (allAlignedStateS Λ N (0 : Fin (N + 1))))).re =
      (dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (allAlignedStateS Λ N (Fin.last N)))).re := by
  rw [allAlignedStateS_zero_heisenbergToyHamiltonianS_expectation,
      allAlignedStateS_last_heisenbergToyHamiltonianS_expectation]

end LatticeSystem.Quantum
