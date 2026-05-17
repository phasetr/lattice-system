import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelAllAlignedOrtho

/-!
# `(⟨Φ_↑⟩ + ⟨Φ_Néel⟩).re = 0` unconditionally

The all-up and Néel state expectations of the toy Heisenberg Hamiltonian
sum to zero:

  `(⟨Φ_↑|Ĥ_toy|Φ_↑⟩ + ⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩).re = 0`

unconditionally. From the explicit values
`⟨Φ_↑⟩.re = +|A|·|¬A|·N²/2` and `⟨Φ_Néel⟩.re = −|A|·|¬A|·N²/2`.

Reflects the symmetry of the toy Hamiltonian between the two extreme
configurations (all-up vs alternating).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **All-up + Néel expectations sum to 0** unconditionally. -/
theorem heisenbergToyHamiltonianS_allAligned_zero_add_neel_expectation_re_eq_zero
    [Nonempty Λ] (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (allAlignedStateS Λ N (0 : Fin (N + 1))))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (allAlignedStateS Λ N (0 : Fin (N + 1)))) +
          dotProduct (star (neelStateOfS A N))
            ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
              (neelStateOfS A N))).re = 0 := by
  rw [allAlignedStateS_zero_heisenbergToyHamiltonianS_expectation,
      neelStateOfS_heisenbergToyHamiltonianS_expectation]
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, zero_mul, add_zero, sub_zero, zero_sub,
    neg_zero, zero_div]
  ring

end LatticeSystem.Quantum
