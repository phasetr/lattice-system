import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeelExpectations
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# Energy gap between Néel-state expectation and predicted symmetric minimum

We compare two quantities both expressible in closed form:

- `<Φ_Néel(A, N) | Ĥ_toy_S | Φ_Néel(A, N)> = −|A|·|¬A|·N²/2`
  (PR #1369 `neelStateOfS_heisenbergToyHamiltonianS_expectation`).
- `bipartiteToyMinEnergyPredictedSymm A N
   = −|A|·|¬A|·N²/2 − min(|A|, |¬A|)·N`.

The difference (Néel expectation minus predicted minimum) is exactly

  `min(|A|, |¬A|) · N ≥ 0`,

so the Néel state's energy is above the predicted minimum by this
amount. The gap vanishes at saturated edges (`min = 0`) and is
maximised at balanced sublattices (`min = |Λ|/2`).

This is consistent with Tasaki §2.5 Theorem 2.3: the Néel state is
a candidate ground state, but its energy expectation differs from
the true ground-state energy by a non-negative gap coming from the
sublattice-Casimir diagonal terms.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (A : Λ → Bool) (N : ℕ)

/-- **Néel expectation minus predicted-symm minimum equals
`min(|A|, |¬A|) · N`**.

The Néel state's toy-Hamiltonian expectation is above the
symmetric predicted minimum by exactly the minor-sublattice-count
times `N` term. -/
theorem neelStateOfS_heisenbergToyHamiltonianS_expectation_sub_predictedSymm :
    dotProduct (star (neelStateOfS A N))
        ((heisenbergToyHamiltonianS (Λ := Λ) A N).mulVec
          (neelStateOfS A N)) -
      bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N =
      ((Nat.min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
        (N : ℂ)) := by
  rw [neelStateOfS_heisenbergToyHamiltonianS_expectation]
  unfold bipartiteToyMinEnergyPredictedSymm
  ring

end LatticeSystem.Quantum
