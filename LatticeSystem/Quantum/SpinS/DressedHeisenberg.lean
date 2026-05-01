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

/-- Dressed Heisenberg with the trivial (false) sublattice indicator
reduces to the plain Heisenberg matrix element: no Marshall-sign
factors fire. -/
theorem dressedHeisenbergS_A_false (J : V → V → ℂ) (N : ℕ)
    (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS (fun _ : V => false) J N σ σ' =
      (heisenbergHamiltonianS J N) σ σ' := by
  unfold dressedHeisenbergS
  rw [marshallSignS_eq_one_of_A_false, marshallSignS_eq_one_of_A_false,
      one_mul, one_mul]

/-- For a real-coupled Heisenberg Hamiltonian, the dressed matrix
element is symmetric under σ ↔ σ' (combined with complex conjugation).
This is the matrix-level reflection symmetry that makes the dressed
matrix Hermitian. -/
theorem dressedHeisenbergS_star_swap
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y)
    (σ σ' : V → Fin (N + 1)) :
    star (dressedHeisenbergS A J N σ' σ) = dressedHeisenbergS A J N σ σ' := by
  unfold dressedHeisenbergS
  rw [star_mul, star_mul]
  rw [marshallSignS_star, marshallSignS_star]
  -- Now: star (heisenberg σ' σ) * (sign σ * sign σ') = sign σ * sign σ' * heisenberg σ σ'.
  -- Heisenberg Hermiticity: star (H σ' σ) = (Hᴴ) σ σ' = H σ σ' (since H is Hermitian).
  have hH := heisenbergHamiltonianS_isHermitian_of_real (Λ := V) hreal N
  have hsym : star ((heisenbergHamiltonianS J N) σ' σ) =
      (heisenbergHamiltonianS J N) σ σ' := by
    have := hH.apply σ σ'
    -- `IsHermitian.apply : star (M b a) = M a b`.
    exact this
  rw [hsym]
  ring

/-- Diagonal dressed-Heisenberg matrix elements are real for real
coupling: applying `dressedHeisenbergS_star_swap` at `σ = σ'`. -/
theorem dressedHeisenbergS_diag_star
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y)
    (σ : V → Fin (N + 1)) :
    star (dressedHeisenbergS A J N σ σ) = dressedHeisenbergS A J N σ σ :=
  dressedHeisenbergS_star_swap A N hreal σ σ

/-- The diagonal of `dressedHeisenbergS` has zero imaginary part for
real coupling — equivalent to "the diagonal is real" in concrete
`Complex.im = 0` form. -/
theorem dressedHeisenbergS_diag_im_zero
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y)
    (σ : V → Fin (N + 1)) :
    (dressedHeisenbergS A J N σ σ).im = 0 := by
  have hstar := dressedHeisenbergS_diag_star A N hreal σ
  -- `Complex.conj z = z ↔ z.im = 0` is the standard fact.
  have := Complex.conj_eq_iff_im.mp hstar
  exact this

/-- Diagonal `dressedHeisenbergS` equals its real-part embedding: a
useful form for converting to a real-valued matrix. -/
theorem dressedHeisenbergS_diag_eq_ofReal
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y)
    (σ : V → Fin (N + 1)) :
    dressedHeisenbergS A J N σ σ =
      ((dressedHeisenbergS A J N σ σ).re : ℂ) := by
  apply Complex.ext <;> simp [dressedHeisenbergS_diag_im_zero A N hreal σ]

/-- Dressed Heisenberg with zero coupling has zero matrix elements
(the underlying Heisenberg Hamiltonian is the zero operator). -/
theorem dressedHeisenbergS_zero_J
    (A : V → Bool) (N : ℕ) (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS A (fun _ _ : V => (0 : ℂ)) N σ σ' = 0 := by
  unfold dressedHeisenbergS heisenbergHamiltonianS
  simp

/-- Dressed Heisenberg is additive in the coupling. -/
theorem dressedHeisenbergS_add_J
    (A : V → Bool) (J J' : V → V → ℂ) (N : ℕ) (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS A (fun x y => J x y + J' x y) N σ σ' =
      dressedHeisenbergS A J N σ σ' + dressedHeisenbergS A J' N σ σ' := by
  unfold dressedHeisenbergS
  rw [heisenbergHamiltonianS_add]
  rw [Matrix.add_apply]
  ring

end LatticeSystem.Quantum
