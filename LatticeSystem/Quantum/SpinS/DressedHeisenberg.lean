import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.MarshallSign
import LatticeSystem.Lattice.Graph
import Mathlib.Combinatorics.SimpleGraph.Basic

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

/-- Definitional unfolding of `dressedHeisenbergS`. -/
theorem dressedHeisenbergS_def
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS A J N σ σ' =
      marshallSignS A σ * marshallSignS A σ' *
        (heisenbergHamiltonianS J N) σ σ' := rfl

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

/-- Dressed Heisenberg is homogeneous in the coupling. -/
theorem dressedHeisenbergS_smul_J
    (A : V → Bool) (c : ℂ) (J : V → V → ℂ) (N : ℕ) (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS A (fun x y => c * J x y) N σ σ' =
      c * dressedHeisenbergS A J N σ σ' := by
  unfold dressedHeisenbergS
  rw [heisenbergHamiltonianS_smul]
  rw [Matrix.smul_apply, smul_eq_mul]
  ring

/-- Dressed Heisenberg negation in coupling: `dressed (-J) = -dressed J`. -/
theorem dressedHeisenbergS_neg_J
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS A (fun x y => -(J x y)) N σ σ' =
      -(dressedHeisenbergS A J N σ σ') := by
  rw [show (fun x y : V => -(J x y)) = (fun x y : V => (-1 : ℂ) * J x y) from by
    funext x y; ring]
  rw [dressedHeisenbergS_smul_J]
  ring

/-- Dressed Heisenberg subtraction in coupling. -/
theorem dressedHeisenbergS_sub_J
    (A : V → Bool) (J J' : V → V → ℂ) (N : ℕ) (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergS A (fun x y => J x y - J' x y) N σ σ' =
      dressedHeisenbergS A J N σ σ' - dressedHeisenbergS A J' N σ σ' := by
  rw [show (fun x y : V => J x y - J' x y) =
        (fun x y : V => J x y + (-(J' x y))) from by
    funext x y; ring]
  rw [dressedHeisenbergS_add_J, dressedHeisenbergS_neg_J]
  ring

/-- If the underlying Heisenberg matrix element is zero, the dressed
matrix element is zero. -/
theorem dressedHeisenbergS_zero_of_heisenberg_zero
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ σ' : V → Fin (N + 1)}
    (h : (heisenbergHamiltonianS J N) σ σ' = 0) :
    dressedHeisenbergS A J N σ σ' = 0 := by
  unfold dressedHeisenbergS
  rw [h, mul_zero]

/-- The Marshall-dressed Heisenberg Hamiltonian as a many-body matrix. -/
noncomputable def dressedHeisenbergSMatrix
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) :
    ManyBodyOpS V N :=
  fun σ σ' => dressedHeisenbergS A J N σ σ'

/-- Definitional unfolding of `dressedHeisenbergSMatrix`. -/
theorem dressedHeisenbergSMatrix_def
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) :
    dressedHeisenbergSMatrix A J N =
      (fun σ σ' => dressedHeisenbergS A J N σ σ') := rfl

/-- Component-wise unfolding of `dressedHeisenbergSMatrix`. -/
theorem dressedHeisenbergSMatrix_apply
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergSMatrix A J N σ σ' = dressedHeisenbergS A J N σ σ' := rfl

/-- The dressed Heisenberg matrix is zero when the coupling is zero. -/
theorem dressedHeisenbergSMatrix_zero_J (A : V → Bool) (N : ℕ) :
    dressedHeisenbergSMatrix A (fun _ _ : V => (0 : ℂ)) N = 0 := by
  ext σ σ'
  rw [dressedHeisenbergSMatrix_apply, dressedHeisenbergS_zero_J]
  simp

/-- The dressed Heisenberg matrix is additive in the coupling. -/
theorem dressedHeisenbergSMatrix_add_J
    (A : V → Bool) (J J' : V → V → ℂ) (N : ℕ) :
    dressedHeisenbergSMatrix A (fun x y => J x y + J' x y) N =
      dressedHeisenbergSMatrix A J N + dressedHeisenbergSMatrix A J' N := by
  ext σ σ'
  rw [dressedHeisenbergSMatrix_apply, dressedHeisenbergS_add_J]
  simp [dressedHeisenbergSMatrix_apply]

/-- The dressed Heisenberg matrix is homogeneous in the coupling. -/
theorem dressedHeisenbergSMatrix_smul_J
    (A : V → Bool) (c : ℂ) (J : V → V → ℂ) (N : ℕ) :
    dressedHeisenbergSMatrix A (fun x y => c * J x y) N =
      c • dressedHeisenbergSMatrix A J N := by
  ext σ σ'
  rw [dressedHeisenbergSMatrix_apply, dressedHeisenbergS_smul_J]
  simp [dressedHeisenbergSMatrix_apply]

/-- The dressed Heisenberg matrix negates with the coupling. -/
theorem dressedHeisenbergSMatrix_neg_J
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) :
    dressedHeisenbergSMatrix A (fun x y => -(J x y)) N =
      -(dressedHeisenbergSMatrix A J N) := by
  ext σ σ'
  rw [dressedHeisenbergSMatrix_apply, dressedHeisenbergS_neg_J]
  simp [dressedHeisenbergSMatrix_apply]

/-- The dressed Heisenberg matrix is anti-distributive over subtraction
in the coupling. -/
theorem dressedHeisenbergSMatrix_sub_J
    (A : V → Bool) (J J' : V → V → ℂ) (N : ℕ) :
    dressedHeisenbergSMatrix A (fun x y => J x y - J' x y) N =
      dressedHeisenbergSMatrix A J N - dressedHeisenbergSMatrix A J' N := by
  ext σ σ'
  rw [dressedHeisenbergSMatrix_apply, dressedHeisenbergS_sub_J]
  simp [dressedHeisenbergSMatrix_apply]

/-- The diagonal of the dressed Heisenberg matrix equals the diagonal
of the plain Heisenberg matrix (Marshall signs cancel as `(±1)^2 = 1`). -/
theorem dressedHeisenbergSMatrix_apply_diag
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (σ : V → Fin (N + 1)) :
    dressedHeisenbergSMatrix A J N σ σ =
      (heisenbergHamiltonianS J N) σ σ := by
  rw [dressedHeisenbergSMatrix_apply, dressedHeisenbergS_diag]

/-- The dressed Heisenberg matrix as a product: `dressed σ' σ =
sign(σ') · sign(σ) · heisenberg σ' σ`. -/
theorem dressedHeisenbergSMatrix_apply_eq_smul
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (σ' σ : V → Fin (N + 1)) :
    dressedHeisenbergSMatrix A J N σ' σ =
      marshallSignS A σ' * marshallSignS A σ *
        (heisenbergHamiltonianS J N) σ' σ := by
  rfl

/-- For real coupling, the dressed matrix is Hermitian. -/
theorem dressedHeisenbergSMatrix_isHermitian
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y) :
    (dressedHeisenbergSMatrix A J N).IsHermitian := by
  ext σ σ'
  simp only [Matrix.conjTranspose_apply, dressedHeisenbergSMatrix_apply]
  exact dressedHeisenbergS_star_swap A N hreal σ σ'

/-- Hermiticity of the dressed Heisenberg matrix on a graph-derived
coupling, with a real complex edge weight. The hypothesis
`star J = J` ensures `couplingOf G J` is entry-wise real
(`couplingOf_real`), which then feeds into
`dressedHeisenbergSMatrix_isHermitian`. -/
theorem dressedHeisenbergSMatrix_couplingOf_isHermitian
    (A : V → Bool) (G : SimpleGraph V) [DecidableRel G.Adj]
    {J : ℂ} (hJ : star J = J) (N : ℕ) :
    (dressedHeisenbergSMatrix A
        (LatticeSystem.Lattice.couplingOf G J) N).IsHermitian :=
  dressedHeisenbergSMatrix_isHermitian A N
    (LatticeSystem.Lattice.couplingOf_real G hJ)

/-- Dressed Heisenberg on the open chain — Hermiticity. -/
theorem dressedHeisenbergSMatrix_chain_isHermitian
    (M : ℕ) (A : Fin (M + 1) → Bool) (J : ℝ) (N : ℕ) :
    (dressedHeisenbergSMatrix A
        (LatticeSystem.Lattice.couplingOf
          (SimpleGraph.pathGraph (M + 1)) (-(J : ℂ))) N).IsHermitian :=
  dressedHeisenbergSMatrix_couplingOf_isHermitian A _
    (by simp : star (-(J : ℂ)) = -(J : ℂ)) N

/-- Dressed Heisenberg on the periodic chain — Hermiticity. -/
theorem dressedHeisenbergSMatrix_periodicChain_isHermitian
    (M : ℕ) (A : Fin (M + 2) → Bool) (J : ℝ) (N : ℕ) :
    (dressedHeisenbergSMatrix A
        (LatticeSystem.Lattice.couplingOf
          (SimpleGraph.cycleGraph (M + 2)) (-(J : ℂ))) N).IsHermitian :=
  dressedHeisenbergSMatrix_couplingOf_isHermitian A _
    (by simp : star (-(J : ℂ)) = -(J : ℂ)) N

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

/-- The real-part dressed Heisenberg matrix is additive in the
coupling. -/
theorem dressedHeisenbergSReMatrix_add_J
    (A : V → Bool) (J J' : V → V → ℂ) (N : ℕ)
    (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix A (fun x y => J x y + J' x y) N σ σ' =
      dressedHeisenbergSReMatrix A J N σ σ' +
        dressedHeisenbergSReMatrix A J' N σ σ' := by
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergS_add_J]
  simp [dressedHeisenbergSReMatrix_apply]

/-- The real-part dressed Heisenberg matrix negates with the
coupling. -/
theorem dressedHeisenbergSReMatrix_neg_J
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix A (fun x y => -(J x y)) N σ σ' =
      -(dressedHeisenbergSReMatrix A J N σ σ') := by
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergS_neg_J]
  simp [dressedHeisenbergSReMatrix_apply]

/-- For real coupling, the real-part dressed Heisenberg matrix is
Hermitian (which for a real-valued matrix is equivalent to
symmetry). -/
theorem dressedHeisenbergSReMatrix_isHermitian
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y) :
    (dressedHeisenbergSReMatrix A J N).IsHermitian := by
  ext σ σ'
  simp only [Matrix.conjTranspose_apply, star_trivial]
  have h := dressedHeisenbergSReMatrix_isSymm A N hreal
  exact congrFun (congrFun h σ) σ'

/-- Real-part dressed Heisenberg matrix Hermiticity for a graph-derived
coupling. -/
theorem dressedHeisenbergSReMatrix_couplingOf_isHermitian
    (A : V → Bool) (G : SimpleGraph V) [DecidableRel G.Adj]
    {J : ℂ} (hJ : star J = J) (N : ℕ) :
    (dressedHeisenbergSReMatrix A
        (LatticeSystem.Lattice.couplingOf G J) N).IsHermitian :=
  dressedHeisenbergSReMatrix_isHermitian A N
    (LatticeSystem.Lattice.couplingOf_real G hJ)

/-- Real-part dressed Heisenberg matrix on the open chain — Hermiticity. -/
theorem dressedHeisenbergSReMatrix_chain_isHermitian
    (M : ℕ) (A : Fin (M + 1) → Bool) (J : ℝ) (N : ℕ) :
    (dressedHeisenbergSReMatrix A
        (LatticeSystem.Lattice.couplingOf
          (SimpleGraph.pathGraph (M + 1)) (-(J : ℂ))) N).IsHermitian :=
  dressedHeisenbergSReMatrix_couplingOf_isHermitian A _
    (by simp : star (-(J : ℂ)) = -(J : ℂ)) N

/-- Real-part dressed Heisenberg matrix on the periodic chain — Hermiticity. -/
theorem dressedHeisenbergSReMatrix_periodicChain_isHermitian
    (M : ℕ) (A : Fin (M + 2) → Bool) (J : ℝ) (N : ℕ) :
    (dressedHeisenbergSReMatrix A
        (LatticeSystem.Lattice.couplingOf
          (SimpleGraph.cycleGraph (M + 2)) (-(J : ℂ))) N).IsHermitian :=
  dressedHeisenbergSReMatrix_couplingOf_isHermitian A _
    (by simp : star (-(J : ℂ)) = -(J : ℂ)) N

end LatticeSystem.Quantum
