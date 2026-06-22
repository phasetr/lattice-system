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

/-- Definitional unfolding of `dressedHeisenbergSReMatrix`. -/
theorem dressedHeisenbergSReMatrix_def
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) :
    dressedHeisenbergSReMatrix A J N =
      fun σ σ' => (dressedHeisenbergS A J N σ σ').re := rfl

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

/-- The real-part dressed Heisenberg matrix is zero when the coupling
is zero (since the underlying Hamiltonian is zero). -/
theorem dressedHeisenbergSReMatrix_zero_J
    (A : V → Bool) (N : ℕ) :
    dressedHeisenbergSReMatrix A (fun _ _ : V => (0 : ℂ)) N = 0 := by
  ext σ σ'
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergS_zero_J]
  simp

/-- For trivial spin (`N = 0`), the real-part dressed Heisenberg
matrix is zero. -/
theorem dressedHeisenbergSReMatrix_N_zero
    (A : V → Bool) (J : V → V → ℂ) :
    dressedHeisenbergSReMatrix A J 0 = 0 := by
  ext σ σ'
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergS_N_zero]
  simp

/-- With the trivial sublattice indicator (`fun _ => false`), the
real-part dressed Heisenberg matrix equals the real-part of the plain
Heisenberg matrix. -/
theorem dressedHeisenbergSReMatrix_A_false (J : V → V → ℂ) (N : ℕ)
    (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix (fun _ : V => false) J N σ σ' =
      ((heisenbergHamiltonianS J N) σ σ').re := by
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergS_A_false]

/-- The diagonal of the real-part dressed Heisenberg matrix equals
the real-part of the plain Heisenberg diagonal: the Marshall sign
squares to 1, so the dressing does not change the diagonal. -/
theorem dressedHeisenbergSReMatrix_diag (A : V → Bool) (J : V → V → ℂ)
    (N : ℕ) (σ : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix A J N σ σ =
      ((heisenbergHamiltonianS J N) σ σ).re := by
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergS_diag]

/-- The real-part dressed Heisenberg matrix is independent of the
sublattice indicator on its diagonal. -/
theorem dressedHeisenbergSReMatrix_diag_indep (A A' : V → Bool)
    (J : V → V → ℂ) (N : ℕ) (σ : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix A J N σ σ =
      dressedHeisenbergSReMatrix A' J N σ σ := by
  rw [dressedHeisenbergSReMatrix_diag, dressedHeisenbergSReMatrix_diag]

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

/-- For symmetric coupling `J x y = J y x`, the dressed Heisenberg
matrix `dressedHeisenbergS A J N` is symmetric on the configuration
basis. The Marshall sign factor `sign(σ')·sign(σ)` is symmetric in
`(σ', σ)`, and the underlying Heisenberg is symmetric for symmetric
coupling. -/
theorem dressedHeisenbergS_apply_swap_of_symm
    (A : V → Bool) {J : V → V → ℂ}
    (hsym : ∀ x y, J x y = J y x) (N : ℕ)
    (σ' σ : V → Fin (N + 1)) :
    dressedHeisenbergS A J N σ' σ =
      dressedHeisenbergS A J N σ σ' := by
  unfold dressedHeisenbergS
  rw [heisenbergHamiltonianS_apply_swap_of_symm hsym N σ' σ]
  ring

/-- For symmetric coupling, the real-part dressed Heisenberg matrix
is symmetric on the configuration basis. -/
theorem dressedHeisenbergSReMatrix_apply_swap_of_symm
    (A : V → Bool) {J : V → V → ℂ}
    (hsym : ∀ x y, J x y = J y x) (N : ℕ)
    (σ' σ : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix A J N σ' σ =
      dressedHeisenbergSReMatrix A J N σ σ' := by
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergSReMatrix_apply,
      dressedHeisenbergS_apply_swap_of_symm A hsym N σ' σ]


end LatticeSystem.Quantum
