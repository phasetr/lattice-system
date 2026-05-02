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

/-- All entries of `dressedHeisenbergS` have zero imaginary part for
coupling whose entries are real. -/
theorem dressedHeisenbergS_apply_im_zero
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, (J x y).im = 0)
    (σ' σ : V → Fin (N + 1)) :
    (dressedHeisenbergS A J N σ' σ).im = 0 := by
  unfold dressedHeisenbergS
  rw [Complex.mul_im, Complex.mul_im]
  rw [marshallSignS_im, marshallSignS_im]
  rw [heisenbergHamiltonianS_apply_im_zero (Λ := V) N hreal]
  ring

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

/-- For trivial spin (`N = 0`, `S = 0`), every dressed Heisenberg
matrix element vanishes (the underlying Heisenberg is zero). -/
theorem dressedHeisenbergS_N_zero
    (A : V → Bool) (J : V → V → ℂ) (σ σ' : V → Fin 1) :
    dressedHeisenbergS A J 0 σ σ' = 0 := by
  unfold dressedHeisenbergS
  rw [heisenbergHamiltonianS_N_zero (Λ := V) J]
  simp

/-- The diagonal real part of `dressedHeisenbergS` equals the
diagonal real part of `heisenbergHamiltonianS`. -/
theorem dressedHeisenbergS_diag_re
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (σ : V → Fin (N + 1)) :
    (dressedHeisenbergS A J N σ σ).re =
      ((heisenbergHamiltonianS J N) σ σ).re := by
  rw [dressedHeisenbergS_diag]

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

/-- For trivial spin (`N = 0`), the dressed Heisenberg matrix is zero. -/
theorem dressedHeisenbergSMatrix_N_zero
    (A : V → Bool) (J : V → V → ℂ) :
    dressedHeisenbergSMatrix A J 0 = 0 := by
  ext σ σ'
  rw [dressedHeisenbergSMatrix_apply, dressedHeisenbergS_N_zero]
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

/-- Applying the dressed Heisenberg matrix to a basis vector and
reading the result at configuration `τ` yields the matrix element
`dressedMatrix τ σ`. -/
theorem dressedHeisenbergSMatrix_mulVec_basisVecS_apply
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (σ τ : V → Fin (N + 1)) :
    (dressedHeisenbergSMatrix A J N).mulVec (basisVecS σ) τ =
      dressedHeisenbergSMatrix A J N τ σ := by
  classical
  change ∑ σ' : V → Fin (N + 1),
      dressedHeisenbergSMatrix A J N τ σ' * basisVecS σ σ' =
        dressedHeisenbergSMatrix A J N τ σ
  simp_rw [basisVecS_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ σ
      (fun σ' => dressedHeisenbergSMatrix A J N τ σ')]
  simp

/-- Like the plain Heisenberg, the dressed matrix element vanishes
when the two configurations have different magnetization quantum
numbers. The Marshall sign factors do not change the support. -/
theorem dressedHeisenbergSMatrix_apply_eq_zero_of_mag_ne
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    (h : magEigenvalueS σ ≠ magEigenvalueS σ') :
    dressedHeisenbergSMatrix A J N σ' σ = 0 := by
  rw [dressedHeisenbergSMatrix_apply_eq_smul]
  rw [heisenbergHamiltonianS_apply_eq_zero_of_mag_ne (Λ := V) J N h]
  ring

/-- The dressed Heisenberg matrix applied to a basis state lies in
the magnetization subspace `magSubspaceS V N (magEigenvalueS σ)`. -/
theorem dressedHeisenbergSMatrix_mulVec_basisVecS_mem_magSubspaceS
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (σ : V → Fin (N + 1)) :
    (dressedHeisenbergSMatrix A J N).mulVec (basisVecS σ) ∈
      magSubspaceS V N (magEigenvalueS σ) := by
  rw [mem_magSubspaceS_iff]
  funext τ
  classical
  change ∑ ρ, (totalSpinSOp3 V N) τ ρ *
      (dressedHeisenbergSMatrix A J N).mulVec (basisVecS σ) ρ =
    (magEigenvalueS σ •
      (dressedHeisenbergSMatrix A J N).mulVec (basisVecS σ)) τ
  rw [Finset.sum_eq_single τ]
  · rw [totalSpinSOp3_apply_diag,
        dressedHeisenbergSMatrix_mulVec_basisVecS_apply,
        Pi.smul_apply, smul_eq_mul,
        dressedHeisenbergSMatrix_mulVec_basisVecS_apply]
    by_cases hmag : magEigenvalueS τ = magEigenvalueS σ
    · rw [hmag]
    · have hzero := dressedHeisenbergSMatrix_apply_eq_zero_of_mag_ne
        A J N (Ne.symm hmag)
      rw [hzero]; ring
  · intro ρ _ hρ
    rw [totalSpinSOp3_apply_off_diag (Ne.symm hρ), zero_mul]
  · intro hτ; exact (hτ (Finset.mem_univ τ)).elim

/-- The dressed Heisenberg matrix applied to a Marshall-dressed basis
state lies in the same magnetization subspace as the underlying
basis vector. -/
theorem dressedHeisenbergSMatrix_mulVec_marshallDressedBasisS_mem_magSubspaceS
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (σ : V → Fin (N + 1)) :
    (dressedHeisenbergSMatrix A J N).mulVec (marshallDressedBasisS A σ) ∈
      magSubspaceS V N (magEigenvalueS σ) := by
  unfold marshallDressedBasisS
  rw [Matrix.mulVec_smul]
  exact (magSubspaceS V N (magEigenvalueS σ)).smul_mem _
    (dressedHeisenbergSMatrix_mulVec_basisVecS_mem_magSubspaceS A J N σ)

/-- The dressed Heisenberg matrix commutes with `Ŝ_tot^{(3)}`. -/
theorem dressedHeisenbergSMatrix_commute_totalSpinSOp3
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) :
    Commute (dressedHeisenbergSMatrix A J N) (totalSpinSOp3 V N) := by
  unfold Commute SemiconjBy
  ext σ' σ
  classical
  -- Compute LHS: ∑ τ, dressed σ' τ * S^z τ σ collapses to dressed σ' σ * magEig σ.
  have hL : (dressedHeisenbergSMatrix A J N * totalSpinSOp3 V N) σ' σ =
      dressedHeisenbergSMatrix A J N σ' σ * magEigenvalueS σ := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single σ
      (fun τ _ hτ => by
        rw [show (totalSpinSOp3 V N) τ σ = 0 from
          totalSpinSOp3_apply_off_diag hτ]; ring)
      (fun hσ => (hσ (Finset.mem_univ σ)).elim)]
    rw [totalSpinSOp3_apply_diag]
  have hR : (totalSpinSOp3 V N * dressedHeisenbergSMatrix A J N) σ' σ =
      magEigenvalueS σ' * dressedHeisenbergSMatrix A J N σ' σ := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single σ'
      (fun τ _ hτ => by
        rw [show (totalSpinSOp3 V N) σ' τ = 0 from
          totalSpinSOp3_apply_off_diag (Ne.symm hτ)]; ring)
      (fun hσ => (hσ (Finset.mem_univ σ')).elim)]
    rw [totalSpinSOp3_apply_diag]
  rw [hL, hR]
  by_cases hmag : magEigenvalueS σ = magEigenvalueS σ'
  · rw [hmag]; ring
  · have hzero := dressedHeisenbergSMatrix_apply_eq_zero_of_mag_ne
      A J N hmag
    rw [hzero]; ring

/-- The dressed Heisenberg matrix preserves each magnetization
subspace: for `v ∈ magSubspaceS V N M`, `(dressedMatrix · v) ∈
magSubspaceS V N M`. -/
theorem dressedHeisenbergSMatrix_mulVec_mem_magSubspaceS
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (M : ℂ)
    {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS V N M) :
    (dressedHeisenbergSMatrix A J N).mulVec v ∈ magSubspaceS V N M :=
  mem_magSubspaceS_of_commute M (dressedHeisenbergSMatrix A J N)
    (dressedHeisenbergSMatrix_commute_totalSpinSOp3 A J N).symm hv

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

/-! ## Marshall-dressed `(Ŝ_x · Ŝ_y)` on bipartite raising/lowering pairs -/

/-- **Bipartite Marshall dressing makes the off-diagonal `Ŝ_x · Ŝ_y`
matrix element non-positive**: for `x ∈ A`, `y ∉ A`, configurations
`σ', σ` agreeing off `{x, y}` with the raising shift at `x`
(`σ_x = σ'_x + 1`) and lowering shift at `y` (`σ_y + 1 = σ'_y`), the
dressed spinSDot real part `(marshallSignS A σ' * marshallSignS A σ) *
(Ŝ_x · Ŝ_y) σ' σ` is non-positive.

The Marshall sign factor is `-1` (PR #772), the off-diagonal entry
is positive (PR #781), so the product is non-positive. This is the
key non-positivity needed for the Marshall sign trick (Tasaki Theorem 2.2). -/
theorem marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_x
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = true) (hAy : A y = false)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val)
    (_hy : (σ y).val + 1 = (σ' y).val) :
    ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 := by
  -- Marshall sign factor: bipartite raising at x with A x = true gives -1.
  have hsign : marshallSignS A σ' * marshallSignS A σ = -1 := by
    apply marshallSignS_mul_of_agree_off_two_site_bipartite_x A hxy hAx hAy h
    -- Need: Odd ((σ' x).val + (σ x).val).
    rw [show (σ x).val = (σ' x).val + 1 from hx.symm]
    rw [show (σ' x).val + ((σ' x).val + 1) = 2 * (σ' x).val + 1 from by ring]
    exact ⟨(σ' x).val, rfl⟩
  rw [hsign]
  rw [show ((-1 : ℂ) * (spinSDot x y N : ManyBodyOpS V N) σ' σ).re =
        -((spinSDot x y N : ManyBodyOpS V N) σ' σ).re from by
    rw [Complex.mul_re]
    simp]
  rw [neg_nonpos]
  exact spinSDot_apply_re_nonneg_of_raising_lowering_x hxy N h hx

/-- Symmetric: lowering at `x` direction. -/
theorem marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_x_lowering
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = true) (hAy : A y = false)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val)
    (_hy : (σ' y).val + 1 = (σ y).val) :
    ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 := by
  have hsign : marshallSignS A σ' * marshallSignS A σ = -1 := by
    apply marshallSignS_mul_of_agree_off_two_site_bipartite_x A hxy hAx hAy h
    rw [show (σ' x).val = (σ x).val + 1 from hx.symm]
    rw [show (σ x).val + 1 + (σ x).val = 2 * (σ x).val + 1 from by ring]
    exact ⟨(σ x).val, rfl⟩
  rw [hsign]
  rw [show ((-1 : ℂ) * (spinSDot x y N : ManyBodyOpS V N) σ' σ).re =
        -((spinSDot x y N : ManyBodyOpS V N) σ' σ).re from by
    rw [Complex.mul_re]
    simp]
  rw [neg_nonpos]
  exact spinSDot_apply_re_nonneg_of_raising_lowering_y hxy N h hx

/-- The dressed Heisenberg matrix vanishes on one-site differences.
Direct corollary: dressed = sign × sign × H, and H vanishes there. -/
theorem dressedHeisenbergS_apply_eq_zero_of_one_site_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z : V} (hagree : ∀ k, k ≠ z → σ' k = σ k) (hz : σ' z ≠ σ z) :
    dressedHeisenbergS A J N σ' σ = 0 := by
  unfold dressedHeisenbergS
  rw [heisenbergHamiltonianS_apply_eq_zero_of_one_site_diff
    (Λ := V) J N hagree hz]
  ring

/-- The dressed Heisenberg matrix (as a `ManyBodyOpS`) vanishes on
one-site differences. -/
theorem dressedHeisenbergSMatrix_apply_eq_zero_of_one_site_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z : V} (hagree : ∀ k, k ≠ z → σ' k = σ k) (hz : σ' z ≠ σ z) :
    dressedHeisenbergSMatrix A J N σ' σ = 0 :=
  dressedHeisenbergS_apply_eq_zero_of_one_site_diff A J N hagree hz

/-- The real-part dressed Heisenberg matrix vanishes on one-site
differences. -/
theorem dressedHeisenbergSReMatrix_apply_eq_zero_of_one_site_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z : V} (hagree : ∀ k, k ≠ z → σ' k = σ k) (hz : σ' z ≠ σ z) :
    dressedHeisenbergSReMatrix A J N σ' σ = 0 := by
  rw [dressedHeisenbergSReMatrix_apply,
    dressedHeisenbergS_apply_eq_zero_of_one_site_diff A J N hagree hz]
  simp

/-- Dressed Heisenberg matrix vanishes on three-site differences. -/
theorem dressedHeisenbergS_apply_eq_zero_of_three_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z₁ z₂ z₃ : V}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (hz1 : σ' z₁ ≠ σ z₁) (hz2 : σ' z₂ ≠ σ z₂) (hz3 : σ' z₃ ≠ σ z₃) :
    dressedHeisenbergS A J N σ' σ = 0 := by
  unfold dressedHeisenbergS
  rw [heisenbergHamiltonianS_apply_eq_zero_of_three_diff (Λ := V) J N
    h12 h13 h23 hz1 hz2 hz3]
  ring

/-- Dressed Heisenberg `Matrix` vanishes on three-site differences. -/
theorem dressedHeisenbergSMatrix_apply_eq_zero_of_three_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z₁ z₂ z₃ : V}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (hz1 : σ' z₁ ≠ σ z₁) (hz2 : σ' z₂ ≠ σ z₂) (hz3 : σ' z₃ ≠ σ z₃) :
    dressedHeisenbergSMatrix A J N σ' σ = 0 :=
  dressedHeisenbergS_apply_eq_zero_of_three_diff A J N h12 h13 h23 hz1 hz2 hz3

/-- Real-part dressed Heisenberg matrix vanishes on three-site differences. -/
theorem dressedHeisenbergSReMatrix_apply_eq_zero_of_three_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z₁ z₂ z₃ : V}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (hz1 : σ' z₁ ≠ σ z₁) (hz2 : σ' z₂ ≠ σ z₂) (hz3 : σ' z₃ ≠ σ z₃) :
    dressedHeisenbergSReMatrix A J N σ' σ = 0 := by
  rw [dressedHeisenbergSReMatrix_apply,
    dressedHeisenbergS_apply_eq_zero_of_three_diff A J N
      h12 h13 h23 hz1 hz2 hz3]
  simp

/-- Symmetric: bipartite case `x ∉ A, y ∈ A`, raising at `x`. -/
theorem marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_y
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = false) (hAy : A y = true)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (_hx : (σ' x).val + 1 = (σ x).val)
    (hy : (σ y).val + 1 = (σ' y).val) :
    ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 := by
  have hsign : marshallSignS A σ' * marshallSignS A σ = -1 := by
    apply marshallSignS_mul_of_agree_off_two_site_bipartite_y A hxy hAx hAy h
    rw [show (σ' y).val = (σ y).val + 1 from hy.symm]
    rw [show (σ y).val + 1 + (σ y).val = 2 * (σ y).val + 1 from by ring]
    exact ⟨(σ y).val, rfl⟩
  rw [hsign]
  rw [show ((-1 : ℂ) * (spinSDot x y N : ManyBodyOpS V N) σ' σ).re =
        -((spinSDot x y N : ManyBodyOpS V N) σ' σ).re from by
    rw [Complex.mul_re]
    simp]
  rw [neg_nonpos]
  exact spinSDot_apply_re_nonneg_of_raising_lowering_x hxy N h _hx

/-- Mirror of `marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_y`:
bipartite case `x ∉ A, y ∈ A`, but lowering at `y` and raising at `x`. -/
theorem marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_y_lowering
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = false) (hAy : A y = true)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val)
    (_hy : (σ' y).val + 1 = (σ y).val) :
    ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 := by
  have hsign : marshallSignS A σ' * marshallSignS A σ = -1 := by
    apply marshallSignS_mul_of_agree_off_two_site_bipartite_y A hxy hAx hAy h
    rw [show (σ' y).val = (σ y).val - 1 from by omega]
    rw [show (σ y).val - 1 + (σ y).val = 2 * (σ y).val - 1 from by omega]
    -- Need: Odd (2 * (σ y).val - 1).
    rcases (σ y).val.eq_zero_or_pos with hzero | hpos
    · -- (σ y).val = 0 forces (σ' y).val + 1 = 0, impossible.
      exfalso
      rw [hzero] at _hy
      omega
    · refine ⟨(σ y).val - 1, ?_⟩
      omega
  rw [hsign]
  rw [show ((-1 : ℂ) * (spinSDot x y N : ManyBodyOpS V N) σ' σ).re =
        -((spinSDot x y N : ManyBodyOpS V N) σ' σ).re from by
    rw [Complex.mul_re]
    simp]
  rw [neg_nonpos]
  exact spinSDot_apply_re_nonneg_of_raising_lowering_y hxy N h hx

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

/-- The complex dressed matrix entry equals the real-embedded
real-part: `dressed σ' σ = ((dressedRe σ' σ : ℝ) : ℂ)` for coupling
with real entries. -/
theorem dressedHeisenbergSMatrix_apply_eq_ofReal_re
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, (J x y).im = 0)
    (σ' σ : V → Fin (N + 1)) :
    dressedHeisenbergSMatrix A J N σ' σ =
      ((dressedHeisenbergSReMatrix A J N σ' σ : ℝ) : ℂ) := by
  rw [dressedHeisenbergSReMatrix_apply]
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im]
    exact dressedHeisenbergS_apply_im_zero A N hreal σ' σ

/-- Matrix-level equality: the complex dressed matrix equals the
ℂ-embedding of the real-valued dressed matrix entry-wise. -/
theorem dressedHeisenbergSMatrix_eq_dressedHeisenbergSReMatrix_complex
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, (J x y).im = 0) :
    dressedHeisenbergSMatrix A J N =
      (dressedHeisenbergSReMatrix A J N).map (fun r : ℝ => (r : ℂ)) := by
  ext σ' σ
  rw [Matrix.map_apply, dressedHeisenbergSMatrix_apply_eq_ofReal_re A N hreal]

/-- **Two-site matrix-element formula for the dressed Heisenberg
matrix**: for `x ≠ y` and configurations `σ', σ` agreeing off `{x, y}`
with `σ' ≠ σ`,

    `dressedHeisenbergS A J N σ' σ
       = (J(x, y) + J(y, x)) ·
           (marshallSignS A σ' · marshallSignS A σ) · (Ŝ_x · Ŝ_y) σ' σ`.

Direct corollary of `heisenbergHamiltonianS_apply_of_off_two_site_agree`
unfolded through the dressed-Heisenberg definition. -/
theorem dressedHeisenbergS_apply_of_off_two_site_agree
    (A : V → Bool) {J : V → V → ℂ} {x y : V} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    dressedHeisenbergS A J N σ' σ =
      (J x y + J y x) * (marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ := by
  unfold dressedHeisenbergS
  rw [heisenbergHamiltonianS_apply_of_off_two_site_agree (Λ := V) hxy N
    hne h]
  ring

/-- **Off-diagonal dressed Heisenberg non-positivity, bipartite raising
case** (Tasaki §2.5 Property (ii) for general spin, raising at `x ∈ A`).

For a bipartite sublattice indicator `A` (`A x = true`, `A y = false`),
real symmetric coupling `J` with `(J x y).re ≥ 0`, and configurations
`σ', σ` agreeing off `{x, y}` exhibiting raising at `x` and lowering
at `y` (`σ' x = σ x + 1`, `σ y = σ' y + 1`), the dressed matrix
element has non-positive real part:

    `Re (dressedHeisenbergS A J N σ' σ) ≤ 0`.

Combines the two-site dressed formula with the spinSDot bipartite
non-positivity (`marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_x`).
The symmetric coupling collapses `J(x, y) + J(y, x)` to `2 · J(x, y)`,
and the realness of `J` lets the real coupling factor through `Re`. -/
theorem dressedHeisenbergS_apply_re_nonpos_bipartite_x
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = true) (hAy : A y = false)
    {J : V → V → ℂ} (hJ_real : (J x y).im = 0) (hJ_nn : 0 ≤ (J x y).re)
    (hJ_sym : J x y = J y x)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val)
    (hy : (σ' y).val + 1 = (σ y).val) :
    (dressedHeisenbergS A J N σ' σ).re ≤ 0 := by
  have hne : σ' ≠ σ := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  -- (J x y + J y x) = 2 * J x y.
  rw [show (J x y + J y x) = 2 * J x y from by rw [← hJ_sym]; ring]
  -- 2 * J x y is real with re = 2 * (J x y).re.
  rw [show (2 : ℂ) * J x y = ((2 * (J x y).re : ℝ) : ℂ) from by
    apply Complex.ext
    · simp
    · simp [hJ_real]]
  -- ((real) * (sign·sign·spinSDot)).re = real · (sign·sign·spinSDot).re.
  rw [show (((2 * (J x y).re : ℝ) : ℂ) *
        (marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ : ℂ) =
      ((2 * (J x y).re : ℝ) : ℂ) *
        ((marshallSignS A σ' * marshallSignS A σ) *
          (spinSDot x y N : ManyBodyOpS V N) σ' σ) from by ring]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  -- Now: (2 · (J x y).re) · (sign·sign·spinSDot).re ≤ 0.
  have hc :
      ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 :=
    marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_x_lowering hxy N A
      hAx hAy h hx hy
  have h2J : 0 ≤ 2 * (J x y).re := by linarith
  nlinarith

/-- **Off-diagonal dressed Heisenberg non-positivity, bipartite case
`x ∉ A, y ∈ A`, raising at `x ∉ A`**. Symmetric to the
`bipartite_x` case with the sublattice roles swapped. -/
theorem dressedHeisenbergS_apply_re_nonpos_bipartite_y
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = false) (hAy : A y = true)
    {J : V → V → ℂ} (hJ_real : (J x y).im = 0) (hJ_nn : 0 ≤ (J x y).re)
    (hJ_sym : J x y = J y x)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val)
    (hy : (σ y).val + 1 = (σ' y).val) :
    (dressedHeisenbergS A J N σ' σ).re ≤ 0 := by
  have hne : σ' ≠ σ := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [show (J x y + J y x) = 2 * J x y from by rw [← hJ_sym]; ring]
  rw [show (2 : ℂ) * J x y = ((2 * (J x y).re : ℝ) : ℂ) from by
    apply Complex.ext
    · simp
    · simp [hJ_real]]
  rw [show (((2 * (J x y).re : ℝ) : ℂ) *
        (marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ : ℂ) =
      ((2 * (J x y).re : ℝ) : ℂ) *
        ((marshallSignS A σ' * marshallSignS A σ) *
          (spinSDot x y N : ManyBodyOpS V N) σ' σ) from by ring]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hc :
      ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 :=
    marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_y hxy N A
      hAx hAy h hx hy
  have h2J : 0 ≤ 2 * (J x y).re := by linarith
  nlinarith

/-- Mirror of `dressedHeisenbergS_apply_re_nonpos_bipartite_x`:
bipartite case `x ∈ A, y ∉ A`, but lowering at `x` and raising at `y`. -/
theorem dressedHeisenbergS_apply_re_nonpos_bipartite_x_lowering
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = true) (hAy : A y = false)
    {J : V → V → ℂ} (hJ_real : (J x y).im = 0) (hJ_nn : 0 ≤ (J x y).re)
    (hJ_sym : J x y = J y x)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val)
    (hy : (σ y).val + 1 = (σ' y).val) :
    (dressedHeisenbergS A J N σ' σ).re ≤ 0 := by
  have hne : σ' ≠ σ := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [show (J x y + J y x) = 2 * J x y from by rw [← hJ_sym]; ring]
  rw [show (2 : ℂ) * J x y = ((2 * (J x y).re : ℝ) : ℂ) from by
    apply Complex.ext
    · simp
    · simp [hJ_real]]
  rw [show (((2 * (J x y).re : ℝ) : ℂ) *
        (marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ : ℂ) =
      ((2 * (J x y).re : ℝ) : ℂ) *
        ((marshallSignS A σ' * marshallSignS A σ) *
          (spinSDot x y N : ManyBodyOpS V N) σ' σ) from by ring]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hc :
      ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 :=
    marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_x hxy N A
      hAx hAy h hx hy
  have h2J : 0 ≤ 2 * (J x y).re := by linarith
  nlinarith

/-- Mirror of `dressedHeisenbergS_apply_re_nonpos_bipartite_y`:
bipartite case `x ∉ A, y ∈ A`, but raising at `x` and lowering at `y`. -/
theorem dressedHeisenbergS_apply_re_nonpos_bipartite_y_lowering
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = false) (hAy : A y = true)
    {J : V → V → ℂ} (hJ_real : (J x y).im = 0) (hJ_nn : 0 ≤ (J x y).re)
    (hJ_sym : J x y = J y x)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val)
    (hy : (σ' y).val + 1 = (σ y).val) :
    (dressedHeisenbergS A J N σ' σ).re ≤ 0 := by
  have hne : σ' ≠ σ := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [show (J x y + J y x) = 2 * J x y from by rw [← hJ_sym]; ring]
  rw [show (2 : ℂ) * J x y = ((2 * (J x y).re : ℝ) : ℂ) from by
    apply Complex.ext
    · simp
    · simp [hJ_real]]
  rw [show (((2 * (J x y).re : ℝ) : ℂ) *
        (marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ : ℂ) =
      ((2 * (J x y).re : ℝ) : ℂ) *
        ((marshallSignS A σ' * marshallSignS A σ) *
          (spinSDot x y N : ManyBodyOpS V N) σ' σ) from by ring]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hc :
      ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 :=
    marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_y_lowering hxy N A
      hAx hAy h hx hy
  have h2J : 0 ≤ 2 * (J x y).re := by linarith
  nlinarith

/-- The real-part dressed Heisenberg matrix entry vanishes when the
two configurations have different magnetization quantum numbers. -/
theorem dressedHeisenbergSReMatrix_apply_eq_zero_of_mag_ne
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    (h : magEigenvalueS σ ≠ magEigenvalueS σ') :
    dressedHeisenbergSReMatrix A J N σ' σ = 0 := by
  rw [dressedHeisenbergSReMatrix_apply]
  have hzero : dressedHeisenbergS A J N σ' σ = 0 :=
    dressedHeisenbergSMatrix_apply_eq_zero_of_mag_ne A J N h
  rw [hzero]; simp

/-! ## Off-`{x, y}`-agree vanishing variants (γ-3 prep)

These three lemmas package the vanishing cases of the two-site
matrix-element formula: when σ', σ off-`{x, y}`-agree but the
spinSDot factor is forced to zero by some structural reason, the
dressed-Heisenberg matrix element vanishes too. -/

/-- **Off-`{x, y}`-agree dressed vanishing, magnetization mismatch**:
when σ', σ off-`{x, y}`-agree with σ' ≠ σ but carry different
magnetization quantum numbers, the dressed matrix element vanishes
(via the two-site formula and `spinSDot_apply_eq_zero_of_mag_ne`). -/
theorem dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_of_mag_ne
    (A : V → Bool) {J : V → V → ℂ} {x y : V} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hmag : magEigenvalueS σ ≠ magEigenvalueS σ') :
    dressedHeisenbergS A J N σ' σ = 0 := by
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [spinSDot_apply_eq_zero_of_mag_ne x y N hmag]
  ring

/-- **Off-`{x, y}`-agree dressed vanishing at `x` non-`±1` shift**:
when σ', σ off-`{x, y}`-agree with σ' ≠ σ and σ' x val differs from
σ x val by an amount other than `±1`, the dressed matrix element
vanishes (via the two-site formula and the spinSDot diff-at-x-not-pm1
vanishing lemma). -/
theorem dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_diff_at_x_not_pm1
    (A : V → Bool) {J : V → V → ℂ} {x y : V} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hσx : σ' x ≠ σ x)
    (hxp : (σ' x).val + 1 ≠ (σ x).val)
    (hxm : (σ x).val + 1 ≠ (σ' x).val) :
    dressedHeisenbergS A J N σ' σ = 0 := by
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [spinSDot_apply_eq_zero_of_off_two_site_agree_diff_at_x_not_pm1
    hxy N h hσx hxp hxm]
  ring

/-- **Off-`{x, y}`-agree dressed vanishing at `y` non-`±1` shift**:
symmetric of `..._diff_at_x_not_pm1`. -/
theorem dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_diff_at_y_not_pm1
    (A : V → Bool) {J : V → V → ℂ} {x y : V} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hσy : σ' y ≠ σ y)
    (hyp : (σ' y).val + 1 ≠ (σ y).val)
    (hym : (σ y).val + 1 ≠ (σ' y).val) :
    dressedHeisenbergS A J N σ' σ = 0 := by
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [spinSDot_apply_eq_zero_of_off_two_site_agree_diff_at_y_not_pm1
    hxy N h hσy hyp hym]
  ring

/-- Helper: configurations agreeing off `{x, y}` have equal
magnetizations iff `(σ x).val + (σ y).val = (σ' x).val + (σ' y).val`. -/
private theorem magEigenvalueS_eq_iff_of_off_two_site_agree
    {x y : V} (hxy : x ≠ y) {N : ℕ} {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    magEigenvalueS σ' = magEigenvalueS σ ↔
      (σ' x).val + (σ' y).val = (σ x).val + (σ y).val := by
  classical
  have hsplit : ∀ τ : V → Fin (N + 1),
      magSumS τ =
        (∑ k ∈ ((Finset.univ : Finset V) \ ({x, y} : Finset V)),
            (τ k).val) + ((τ x).val + (τ y).val) := by
    intro τ
    unfold magSumS
    rw [← Finset.sum_sdiff (Finset.subset_univ ({x, y} : Finset V))]
    congr 1
    rw [Finset.sum_insert (Finset.notMem_singleton.mpr hxy),
      Finset.sum_singleton]
  have hrest :
      ∑ k ∈ (Finset.univ : Finset V) \ ({x, y} : Finset V), (σ' k).val =
        ∑ k ∈ (Finset.univ : Finset V) \ ({x, y} : Finset V), (σ k).val := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      not_or, Finset.mem_univ, true_and] at hk
    rw [h k hk.1 hk.2]
  unfold magEigenvalueS
  constructor
  · intro hmag
    have hsumeq : magSumS σ' = magSumS σ := by
      have : ((magSumS σ' : ℂ)) = ((magSumS σ : ℂ)) := by linear_combination -hmag
      exact_mod_cast this
    rw [hsplit σ', hsplit σ, hrest] at hsumeq
    omega
  · intro hxy_sum
    have hsumeq : magSumS σ' = magSumS σ := by
      rw [hsplit σ', hsplit σ, hrest]
      omega
    push_cast [hsumeq]
    ring

/-- **Full off-diagonal dressed Heisenberg non-positivity on a bipartite
bond** (Tasaki §2.5 Property (ii) for general spin, all cases unified):

For `x ≠ y` with bipartite indicator `A x ≠ A y`, real symmetric
coupling `J` with `(J x y).re ≥ 0`, and *any* `σ' ≠ σ` agreeing off
`{x, y}`,

    `Re (dressedHeisenbergS A J N σ' σ) ≤ 0`.

Case analysis on the values of σ', σ at `{x, y}`:
- differ at exactly one site → `dressed = 0` (one_site_diff).
- differ at both, magnetization mismatched → `dressed = 0` (mag_ne).
- differ at both, mag conserved, `|Δσ x| ≠ 1` → `dressed = 0`
  (`diff_at_x_not_pm1`).
- differ at both, mag conserved, `|Δσ x| = 1` → exactly one of the
  four bipartite raising/lowering non-positivity lemmas (γ-2e). -/
theorem dressedHeisenbergS_apply_re_nonpos_of_off_two_site_agree_bipartite
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAne : A x ≠ A y)
    {J : V → V → ℂ} (hJ_real : (J x y).im = 0) (hJ_nn : 0 ≤ (J x y).re)
    (hJ_sym : J x y = J y x)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (dressedHeisenbergS A J N σ' σ).re ≤ 0 := by
  -- Decompose A x ≠ A y into the two Bool sublattice configurations.
  have hA_or :
      (A x = true ∧ A y = false) ∨ (A x = false ∧ A y = true) := by
    have hxbool : A x = true ∨ A x = false := by
      cases A x <;> simp
    have hybool : A y = true ∨ A y = false := by
      cases A y <;> simp
    rcases hxbool with hax | hax <;> rcases hybool with hay | hay
    · exact (hAne (hax.trans hay.symm)).elim
    · exact Or.inl ⟨hax, hay⟩
    · exact Or.inr ⟨hax, hay⟩
    · exact (hAne (hax.trans hay.symm)).elim
  by_cases hσx : σ' x = σ x
  · -- σ' x = σ x; σ' ≠ σ forces difference at y → one_site_diff at y.
    have hσy : σ' y ≠ σ y := by
      intro hσy
      apply hne
      funext k
      by_cases hkx : k = x
      · subst hkx; exact hσx
      · by_cases hky : k = y
        · subst hky; exact hσy
        · exact h k hkx hky
    have hagree_y : ∀ k, k ≠ y → σ' k = σ k := fun k hky => by
      by_cases hkx : k = x
      · subst hkx; exact hσx
      · exact h k hkx hky
    rw [dressedHeisenbergS_apply_eq_zero_of_one_site_diff A J N
      hagree_y hσy]
    simp
  · by_cases hσy : σ' y = σ y
    · -- σ' y = σ y; differ only at x → one_site_diff at x.
      have hagree_x : ∀ k, k ≠ x → σ' k = σ k := fun k hkx => by
        by_cases hky : k = y
        · subst hky; exact hσy
        · exact h k hkx hky
      rw [dressedHeisenbergS_apply_eq_zero_of_one_site_diff A J N
        hagree_x hσx]
      simp
    · -- σ' x ≠ σ x AND σ' y ≠ σ y: both differ.
      -- Case on the difference at x.
      by_cases hxraise : (σ x).val + 1 = (σ' x).val
      · -- σ' x = σ x + 1: raising at x.
        by_cases hylower : (σ' y).val + 1 = (σ y).val
        · -- σ y = σ' y + 1: lowering at y. Mag conserved → use bipartite.
          rcases hA_or with ⟨hAx, hAy⟩ | ⟨hAx, hAy⟩
          · -- A x = true, A y = false.
            exact dressedHeisenbergS_apply_re_nonpos_bipartite_x
              hxy N A hAx hAy hJ_real hJ_nn hJ_sym h hxraise hylower
          · -- A x = false, A y = true.
            exact dressedHeisenbergS_apply_re_nonpos_bipartite_y_lowering
              hxy N A hAx hAy hJ_real hJ_nn hJ_sym h hxraise hylower
        · -- σ y val + 1 ≠ σ' y val. Either raising at y too (mag-ne) or non-pm1.
          by_cases hyraise : (σ y).val + 1 = (σ' y).val
          · -- raising at y too: mag mismatched (both raised).
            have hzero : dressedHeisenbergS A J N σ' σ = 0 := by
              apply dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_of_mag_ne
                A hxy N hne h
              intro hmag
              have hsum := (magEigenvalueS_eq_iff_of_off_two_site_agree
                hxy h).mp hmag.symm
              omega
            rw [hzero]; simp
          · -- σ' y val differs from σ y val by ≥ 2.
            have hzero : dressedHeisenbergS A J N σ' σ = 0 :=
              dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_diff_at_y_not_pm1
                A hxy N hne h hσy hylower hyraise
            rw [hzero]; simp
      · -- (σ x).val + 1 ≠ (σ' x).val.
        by_cases hxlower : (σ' x).val + 1 = (σ x).val
        · -- σ' x val + 1 = σ x val: lowering at x.
          by_cases hyraise : (σ y).val + 1 = (σ' y).val
          · -- raising at y: mag conserved → bipartite.
            rcases hA_or with ⟨hAx, hAy⟩ | ⟨hAx, hAy⟩
            · -- A x = true, A y = false.
              exact dressedHeisenbergS_apply_re_nonpos_bipartite_x_lowering
                hxy N A hAx hAy hJ_real hJ_nn hJ_sym h hxlower hyraise
            · -- A x = false, A y = true.
              exact dressedHeisenbergS_apply_re_nonpos_bipartite_y
                hxy N A hAx hAy hJ_real hJ_nn hJ_sym h hxlower hyraise
          · -- σ y val + 1 ≠ σ' y val.
            by_cases hylower : (σ' y).val + 1 = (σ y).val
            · -- σ' y val + 1 = σ y val: lowering at y too. Mag mismatched.
              have hzero : dressedHeisenbergS A J N σ' σ = 0 := by
                apply dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_of_mag_ne
                  A hxy N hne h
                intro hmag
                have hsum := (magEigenvalueS_eq_iff_of_off_two_site_agree
                  hxy h).mp hmag.symm
                omega
              rw [hzero]; simp
            · -- σ' y differs by ≥ 2 from σ y.
              have hzero : dressedHeisenbergS A J N σ' σ = 0 :=
                dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_diff_at_y_not_pm1
                  A hxy N hne h hσy hylower hyraise
              rw [hzero]; simp
        · -- |σ' x - σ x| ≥ 2.
          have hzero : dressedHeisenbergS A J N σ' σ = 0 :=
            dressedHeisenbergS_apply_eq_zero_of_off_two_site_agree_diff_at_x_not_pm1
              A hxy N hne h hσx hxlower hxraise
          rw [hzero]; simp

end LatticeSystem.Quantum
