import LatticeSystem.Quantum.SpinS.AllAlignedAddNeelExpectationEqZero
import LatticeSystem.Quantum.SpinS.AllUpEqAllDownExpectation

/-!
# `(⟨Φ_↑⟩ + ⟨Φ_↓⟩ + 2·⟨Φ_Néel⟩).re = 0` unconditionally

Three-state sum identity. The all-up, all-down, and Néel state
expectations balance:

  `(⟨Φ_↑|Ĥ_toy|Φ_↑⟩ + ⟨Φ_↓|Ĥ_toy|Φ_↓⟩ + 2·⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re = 0`

unconditionally. Combines PR #3198 (`⟨Φ_↑⟩ + ⟨Φ_Néel⟩ = 0`) with PR
#3202 (`⟨Φ_↑⟩.re = ⟨Φ_↓⟩.re`).

Reflects the toy Hamiltonian's algebraic balance: each saturated state
contributes `+|A|·|¬A|·N²/2`, Néel contributes `−|A|·|¬A|·N²/2`, so
the weighted total is `+|A|·|¬A|·N²/2 + +|A|·|¬A|·N²/2 + 2·(−|A|·|¬A|·N²/2) = 0`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Three-state sum: `(⟨Φ_↑⟩ + ⟨Φ_↓⟩ + 2·⟨Φ_Néel⟩).re = 0`** unconditionally. -/
theorem heisenbergToyHamiltonianS_allUp_add_allDown_add_two_neel_expectation_re_eq_zero
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
        dotProduct (star (allAlignedStateS Λ N (Fin.last N)))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (allAlignedStateS Λ N (Fin.last N))) +
        2 * dotProduct (star (neelStateOfS A N))
          ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
            (neelStateOfS A N))).re = 0 := by
  have h1 := heisenbergToyHamiltonianS_allAligned_zero_add_neel_expectation_re_eq_zero
    (Λ := Λ) (A := A) (N := N)
  have h2 := heisenbergToyHamiltonianS_allAligned_zero_expectation_re_eq_last_expectation_re
    (Λ := Λ) (A := A) (N := N)
  rw [Complex.add_re] at h1
  rw [Complex.add_re, Complex.add_re, Complex.mul_re]
  simp only [Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
  linarith

end LatticeSystem.Quantum
