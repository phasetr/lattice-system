import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.MarshallSign

/-!
# Marshall-dressed spin-`S` Heisenberg matrix elements
(Tasaki §2.5 Phase B-γ γ-2)

For a sublattice indicator `A : V → Bool` and a spin-`S` Heisenberg
Hamiltonian `Ĥ_J`, the **Marshall-dressed matrix element**:

  `dressedHeisenbergS A J N σ σ'
     := marshallSignS A σ * marshallSignS A σ'
        * (heisenbergHamiltonianS J N) σ σ'`.

This is the central object of the Marshall sign trick: the dressing
factor `marshallSignS A σ * marshallSignS A σ'` cancels the
oscillatory sign structure of the off-diagonal Heisenberg matrix
elements, rendering them real and non-positive on bipartite bonds
(Marshall, 1955; Tasaki §2.5 p. 41 Property (ii) for `S = 1/2`).

For general spin, this PR records only the definition. The Marshall
sign trick proper (positivity of the dressed matrix elements) is
deferred to a follow-up PR.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The Marshall-dressed Heisenberg matrix element. -/
noncomputable def dressedHeisenbergS
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    (σ σ' : V → Fin (N + 1)) : ℂ :=
  marshallSignS A σ * marshallSignS A σ' *
    (heisenbergHamiltonianS J N) σ σ'

/-- Diagonal Marshall-dressed matrix element:
`dressedHeisenbergS A J N σ σ = (heisenbergHamiltonianS J N) σ σ`
(since `marshallSignS A σ * marshallSignS A σ = 1` by γ-1e). -/
theorem dressedHeisenbergS_diag (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    (σ : V → Fin (N + 1)) :
    dressedHeisenbergS A J N σ σ =
      (heisenbergHamiltonianS J N) σ σ := by
  unfold dressedHeisenbergS
  rw [marshallSignS_sq, one_mul]

end LatticeSystem.Quantum
