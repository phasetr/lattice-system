import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Néel expectation vs canonical-orientation predicted min: gap = `|¬A|·N`

The Néel-state expectation `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩ = −|A|·|¬A|·N²/2`,
and the canonical predicted min energy `(pmA).re = −|A|·|¬A|·N²/2 −
|¬A|·N`.

Subtracting (the quadratic term cancels):

  `⟨Φ_Néel|Ĥ_toy|Φ_Néel⟩.re − (predicted_min A).re = |¬A|·N`

unconditionally. Direct operator-algebraic bridge between the
Néel-state expectation and the canonical-orientation predicted min
energy.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

set_option linter.style.longLine false in
/-- **Néel expectation sits `|¬A|·N` above the canonical-orientation
predicted min energy**:

  `⟨Φ_Néel(A, N) | Ĥ_toy_S | Φ_Néel(A, N)⟩.re − (predicted_min A).re
   = |¬A|·N`

unconditionally. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_sub_canonical_predicted_re_eq
    (A : Λ → Bool) (N : ℕ) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re -
      (bipartiteToyMinEnergyPredicted (Λ := Λ) A N).re =
      ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation,
      bipartiteToyMinEnergyPredicted_eq_simplified]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im, Complex.div_ofNat_re,
    mul_zero, zero_mul, sub_zero, add_zero]
  ring

end LatticeSystem.Quantum
