import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations

/-!
# Saturated-edge Néel toy-Hamiltonian expectation: `0`

The Néel-state toy-Hamiltonian expectation closed form
(`neelStateOfS_heisenbergToyHamiltonianS_expectation`, γ-4 step 131)
is `<Φ_Néel|Ĥ_toy_S|Φ_Néel> = −|A|·|¬A|·N²/2`. At a saturated edge
(`|¬A| = 0` or `|A| = 0`), this vanishes:

  `(<Φ_Néel|Ĥ_toy_S|Φ_Néel>).re = 0` at `|¬A| = 0` (or `|A| = 0`).

The Néel state has zero energy at saturated edges, matching the
predicted ground-state energy
`bipartiteToyMinEnergyPredictedSymm = 0` (PR #2849/2850 saturated
zero) — confirming that the Néel state IS a ground state at
saturated edges.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Saturated `|¬A| = 0` Néel toy-Hamiltonian expectation = 0**:
`(<Φ_Néel|Ĥ_toy_S|Φ_Néel>).re = 0`. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_zero_of_cardNotA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card = 0) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re = 0 := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation, h]
  simp

/-- **Saturated `|A| = 0` Néel toy-Hamiltonian expectation = 0**:
`(<Φ_Néel|Ĥ_toy_S|Φ_Néel>).re = 0`. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_re_eq_zero_of_cardA_zero
    (A : Λ → Bool) (N : ℕ)
    (h : (Finset.univ.filter (fun x : Λ => A x = true)).card = 0) :
    (dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N))).re = 0 := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation, h]
  simp

end LatticeSystem.Quantum
