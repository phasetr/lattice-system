import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations

/-!
# Néel `<(Ŝ_A)²>` and `<(Ŝ_¬A)²>` expectations: `s_A(s_A+1)` and `s_B(s_B+1)`

The Néel state is an eigenvector of both sublattice Casimirs at
maximum spin (PR #1283 spin-`S` mirror):

  `(Ŝ_A)² · |Φ_Néel⟩ = s_A·(s_A+1) · |Φ_Néel⟩` where `s_A = |A|·N/2`,
  `(Ŝ_¬A)² · |Φ_Néel⟩ = s_B·(s_B+1) · |Φ_Néel⟩` where `s_B = |¬A|·N/2`.

Taking dot products with `star (neelStateOfS A N)` and using
`neelStateOfS_inner_self = 1` yields the expectation values:

  `<Φ_Néel | (Ŝ_A)² | Φ_Néel> = s_A·(s_A+1)`,
  `<Φ_Néel | (Ŝ_¬A)² | Φ_Néel> = s_B·(s_B+1)`.

These confirm that the Néel state has maximum spin on both
sublattices — a key input to Tasaki §2.5 Theorem 2.3 (γ-4): the
Néel state matches the predicted ground-state subspace's
sublattice Casimir constraints exactly.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Néel `(Ŝ_A)²` expectation = `s_A·(s_A+1)` with `s_A = |A|·N/2`**. -/
theorem neelStateOfS_sublatticeSpinSquaredS_expectation (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((sublatticeSpinSquaredS N A).mulVec (neelStateOfS A N)) =
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) + 1)) := by
  rw [sublatticeSpinSquaredS_mulVec_neelStateOfS,
      dotProduct_smul, smul_eq_mul, neelStateOfS_inner_self, mul_one]

/-- **Néel `(Ŝ_¬A)²` expectation = `s_B·(s_B+1)` with `s_B = |¬A|·N/2`**. -/
theorem neelStateOfS_sublatticeSpinSquaredS_complement_expectation
    (A : Λ → Bool) (N : ℕ) :
    dotProduct (star (neelStateOfS A N))
        ((sublatticeSpinSquaredS N (fun x => ! A x)).mulVec (neelStateOfS A N)) =
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) + 1)) := by
  rw [sublatticeSpinSquaredS_complement_mulVec_neelStateOfS,
      dotProduct_smul, smul_eq_mul, neelStateOfS_inner_self, mul_one]

end LatticeSystem.Quantum
