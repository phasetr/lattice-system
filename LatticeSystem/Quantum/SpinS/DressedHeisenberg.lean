import LatticeSystem.Quantum.SpinS.DressedHeisenbergCore

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

/-- The real-part of the dressed Heisenberg matrix as a real-valued
matrix on the multi-site Hilbert space. -/
noncomputable def dressedHeisenbergSReMatrix
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) :
    Matrix (V → Fin (N + 1)) (V → Fin (N + 1)) ℝ :=
  fun σ σ' => (dressedHeisenbergS A J N σ σ').re

/-- Component-wise unfolding. -/
theorem dressedHeisenbergSReMatrix_apply
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix A J N σ σ' =
      (dressedHeisenbergS A J N σ σ').re := rfl

/-- For real coupling, the real-part dressed Heisenberg matrix is
symmetric: `Mᵀ = M`. This follows from the Hermiticity of the
complex dressed Heisenberg matrix combined with reality of the
diagonal/off-diagonal sums. -/
theorem dressedHeisenbergSReMatrix_isSymm
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y) :
    (dressedHeisenbergSReMatrix A J N).IsSymm := by
  ext σ σ'
  simp only [Matrix.transpose_apply, dressedHeisenbergSReMatrix_apply]
  -- Use Hermiticity: star (z σ' σ) = z σ σ'.
  have h := dressedHeisenbergS_star_swap A N hreal σ σ'
  -- `star z = w` in ℂ means `Complex.conj z = w`, hence `z.re = w.re`.
  have : (dressedHeisenbergS A J N σ' σ).re =
      (dressedHeisenbergS A J N σ σ').re := by
    have := congrArg Complex.re h
    simpa using this
  exact this

/-- The diagonal of the real-part dressed Heisenberg matrix equals
the real-part of the plain Heisenberg diagonal: the Marshall sign
squares to 1, so the dressing does not change the diagonal. -/
theorem dressedHeisenbergSReMatrix_diag (A : V → Bool) (J : V → V → ℂ)
    (N : ℕ) (σ : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix A J N σ σ =
      ((heisenbergHamiltonianS J N) σ σ).re := by
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergS_diag]

/-- The real-part dressed Heisenberg matrix at the all-zero configuration
equals the real part of the corresponding Heisenberg diagonal entry. -/
theorem dressedHeisenbergSReMatrix_const_zero
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) :
    dressedHeisenbergSReMatrix A J N (fun _ : V => (0 : Fin (N + 1)))
        (fun _ : V => (0 : Fin (N + 1))) =
      ((heisenbergHamiltonianS J N)
        (fun _ : V => (0 : Fin (N + 1)))
        (fun _ : V => (0 : Fin (N + 1)))).re :=
  dressedHeisenbergSReMatrix_diag A J N _


end LatticeSystem.Quantum
