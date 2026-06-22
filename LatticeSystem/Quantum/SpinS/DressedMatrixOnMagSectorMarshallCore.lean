import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSector

/-!
# Dressed matrix on a magnetization sector, Marshall form (foundation)

Foundational layer extracted from `DressedMatrixOnMagSectorMarshall.lean` for build speed.
This file builds the Heisenberg sector matrix and its eigenvector via the Marshall reverse
transformation.

The inverse Marshall conjugation and the uniqueness on the Heisenberg sector are kept in
the capstone module `DressedMatrixOnMagSectorMarshall.lean`.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Heisenberg sector matrix and its eigenvector via Marshall reverse -/

/-- The real-valued Heisenberg matrix restricted to the magnetization-`M`
sector. -/
noncomputable def heisenbergHamiltonianSReMatrixOnMagSector
    (J : V → V → ℂ) (N : ℕ) (M : ℕ) :
    Matrix (magConfigS V N M) (magConfigS V N M) ℝ :=
  (heisenbergHamiltonianSReMatrix J N).submatrix Subtype.val Subtype.val

/-- Component-wise unfolding. -/
theorem heisenbergHamiltonianSReMatrixOnMagSector_apply
    (J : V → V → ℂ) (N : ℕ) (M : ℕ)
    (σ τ : magConfigS V N M) :
    heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ =
      heisenbergHamiltonianSReMatrix J N σ.1 τ.1 := rfl

/-- The complex Heisenberg Hamiltonian restricted to the magnetization-`M`
sector (as a complex matrix on the subtype `magConfigS V N M`). -/
noncomputable def heisenbergHamiltonianSMatrixOnMagSector
    (J : V → V → ℂ) (N : ℕ) (M : ℕ) :
    Matrix (magConfigS V N M) (magConfigS V N M) ℂ :=
  (heisenbergHamiltonianS J N).submatrix Subtype.val Subtype.val

/-- Component-wise unfolding of the complex sector matrix. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_apply
    (J : V → V → ℂ) (N : ℕ) (M : ℕ)
    (σ τ : magConfigS V N M) :
    heisenbergHamiltonianSMatrixOnMagSector J N M σ τ =
      heisenbergHamiltonianS J N σ.1 τ.1 := rfl

/-- For real coupling, the complex sector matrix entry equals the
real-form sector matrix entry embedded in `ℂ`. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_apply_eq_ofReal
    {J : V → V → ℂ} (N : ℕ) (M : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (σ τ : magConfigS V N M) :
    heisenbergHamiltonianSMatrixOnMagSector J N M σ τ =
      ((heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ : ℝ) : ℂ) := by
  rw [heisenbergHamiltonianSMatrixOnMagSector_apply,
    heisenbergHamiltonianSReMatrixOnMagSector_apply,
    heisenbergHamiltonianSReMatrix_apply]
  exact heisenbergHamiltonianS_apply_eq_ofReal_re N hJ_real σ.1 τ.1

/-- For real coupling, the complex Heisenberg sector matrix is
Hermitian (lifted from the full-space Hermiticity). -/
theorem heisenbergHamiltonianSMatrixOnMagSector_isHermitian
    {J : V → V → ℂ} (N : ℕ) (M : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y) :
    (heisenbergHamiltonianSMatrixOnMagSector J N M).IsHermitian :=
  (heisenbergHamiltonianS_isHermitian_of_real hreal N).submatrix Subtype.val

/-- **Lift a real eigenvector of the real-form sector matrix to a
complex eigenvector of the complex sector matrix**. For real coupling,
if the real-form sector matrix satisfies `M_re v = μ • v`, then the
complex sector matrix satisfies `M_ℂ (v ↑) = μ • (v ↑)` where the
embedding is `(v ↑) σ := (v σ : ℂ)`.

This is the bridge from the PF/MLM real-eigenvector machinery
(PRs #847–#856) to eigenvectors of the actual complex Heisenberg
Hamiltonian on the magnetization sector. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal
    {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec v = μ • v) :
    (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
      (fun σ => (v σ : ℂ)) =
      (μ : ℂ) • (fun σ => (v σ : ℂ)) := by
  funext σ
  have hσ := congrFun hv σ
  -- hσ : ∑ τ, M_re σ τ * v τ = μ * v σ.
  change ∑ τ, heisenbergHamiltonianSMatrixOnMagSector J N M σ τ *
    (v τ : ℂ) = (μ : ℂ) * (v σ : ℂ)
  -- Convert each term from ℂ to ℝ via apply_eq_ofReal.
  have hconv : ∀ τ : magConfigS V N M,
      heisenbergHamiltonianSMatrixOnMagSector J N M σ τ * (v τ : ℂ) =
      ((heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ * v τ : ℝ) : ℂ) := by
    intro τ
    rw [heisenbergHamiltonianSMatrixOnMagSector_apply_eq_ofReal _ _ hJ_real]
    push_cast
    rfl
  rw [Finset.sum_congr rfl (fun τ _ => hconv τ)]
  rw [← Complex.ofReal_sum]
  change ((heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec v σ : ℂ) =
    (μ : ℂ) * (v σ : ℂ)
  rw [hσ]
  change ((μ * v σ : ℝ) : ℂ) = (μ : ℂ) * (v σ : ℂ)
  push_cast
  ring

/-- **Matrix relation: dressed = sign · sign · heisenberg** (real-part
form). For real coupling, the dressed Heisenberg matrix entry at
`(σ, τ)` equals the product of the Marshall signs at `σ` and `τ` with
the plain Heisenberg matrix entry at `(σ, τ)`. -/
theorem dressedHeisenbergSReMatrix_eq_marshallSign_mul_heisenberg
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (σ τ : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix A J N σ τ =
      (marshallSignS A σ).re * (marshallSignS A τ).re *
        heisenbergHamiltonianSReMatrix J N σ τ := by
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergS_def,
    heisenbergHamiltonianSReMatrix_apply]
  -- (sign σ * sign τ * heis σ τ).re = sign σ.re * sign τ.re * heis σ τ.re
  -- since all imaginary parts are 0.
  have hs1 : (marshallSignS A σ).im = 0 := marshallSignS_im A σ
  have hs2 : (marshallSignS A τ).im = 0 := marshallSignS_im A τ
  have hh : (heisenbergHamiltonianS J N σ τ).im = 0 :=
    heisenbergHamiltonianS_apply_im_zero N hJ_real σ τ
  -- Compute the real part of the triple product step by step.
  have h12_re : ((marshallSignS A σ) * (marshallSignS A τ)).re =
      (marshallSignS A σ).re * (marshallSignS A τ).re := by
    rw [Complex.mul_re, hs1]; ring
  have h12_im : ((marshallSignS A σ) * (marshallSignS A τ)).im = 0 := by
    rw [Complex.mul_im, hs1, hs2]; ring
  rw [Complex.mul_re, h12_im, h12_re, hh]
  ring

/-- **Inverse matrix relation: heisenberg = sign · sign · dressed**
(real-part form). Multiplying both sides of the previous lemma by
`sign σ.re * sign τ.re` and using `sign.re² = 1`. -/
theorem heisenbergHamiltonianSReMatrix_eq_marshallSign_mul_dressed
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (σ τ : V → Fin (N + 1)) :
    heisenbergHamiltonianSReMatrix J N σ τ =
      (marshallSignS A σ).re * (marshallSignS A τ).re *
        dressedHeisenbergSReMatrix A J N σ τ := by
  have h := dressedHeisenbergSReMatrix_eq_marshallSign_mul_heisenberg
    A N hJ_real σ τ
  -- h : dressed = sign σ * sign τ * heis.
  -- Multiply both sides by sign σ * sign τ; LHS becomes (sign σ)² * (sign τ)² * heis = heis.
  have hsq_σ : (marshallSignS A σ).re * (marshallSignS A σ).re = 1 :=
    marshallSignS_re_sq A σ
  have hsq_τ : (marshallSignS A τ).re * (marshallSignS A τ).re = 1 :=
    marshallSignS_re_sq A τ
  -- Apply: sign σ.re * sign τ.re * dressed
  --       = sign σ.re * sign τ.re * (sign σ.re * sign τ.re * heis)
  --       = (sign σ.re)² * (sign τ.re)² * heis = heis.
  rw [h]
  ring_nf
  -- After ring_nf the goal is some polynomial identity in sign.re, sign.re, heis.
  -- We need (sign σ.re)² * (sign τ.re)² * heis = heis.
  -- Use marshallSignS_re_sq.
  calc heisenbergHamiltonianSReMatrix J N σ τ
      = 1 * (1 * heisenbergHamiltonianSReMatrix J N σ τ) := by ring
    _ = ((marshallSignS A σ).re * (marshallSignS A σ).re) *
          (((marshallSignS A τ).re * (marshallSignS A τ).re) *
            heisenbergHamiltonianSReMatrix J N σ τ) := by
          rw [hsq_σ, hsq_τ]
    _ = (marshallSignS A σ).re ^ 2 * (marshallSignS A τ).re ^ 2 *
          heisenbergHamiltonianSReMatrix J N σ τ := by ring

/-- **Marshall-sign-conjugation eigenvector theorem** (Tasaki §2.5
Theorem 2.2 ground-state half, Heisenberg form). Given a real eigenvector
`v` of the dressed Heisenberg sector matrix with eigenvalue `μ`, the
Marshall-sign-conjugated vector

  `w τ := (marshallSignS A τ.1).re * v τ`

is an eigenvector of the (un-dressed) Heisenberg sector matrix with the
same eigenvalue `μ`.

Combined with `exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector_legacy`
(γ-3 dressed-form, #850) this gives the Heisenberg-form ground state
on the magnetization sector with the Marshall sign structure. -/
theorem heisenbergHamiltonianSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ • v) :
    (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
      (fun σ => (marshallSignS A σ.1).re * v σ) =
      μ • (fun σ => (marshallSignS A σ.1).re * v σ) := by
  funext σ
  -- Goal: (heis_sec).mulVec w σ = μ * w σ where w τ = sign τ.1.re * v τ.
  have hσ := congrFun hv σ
  -- hσ : dressed_sec.mulVec v σ = μ • v σ = μ * v σ.
  change (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
      (fun τ => (marshallSignS A τ.1).re * v τ) σ =
    μ * ((marshallSignS A σ.1).re * v σ)
  -- Unfold mulVec to a Finset.sum.
  change ∑ τ, heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ *
      ((marshallSignS A τ.1).re * v τ) =
    μ * ((marshallSignS A σ.1).re * v σ)
  -- Substitute heis = sign · sign · dressed at every term.
  have hsum : ∀ τ : magConfigS V N M,
      heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ *
        ((marshallSignS A τ.1).re * v τ) =
      (marshallSignS A σ.1).re *
        (dressedHeisenbergSReMatrixOnMagSector A J N M σ τ * v τ) := by
    intro τ
    rw [heisenbergHamiltonianSReMatrixOnMagSector_apply,
      dressedHeisenbergSReMatrixOnMagSector_apply,
      heisenbergHamiltonianSReMatrix_eq_marshallSign_mul_dressed A N hJ_real]
    have hsq_τ : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    -- LHS = (sign σ.re * sign τ.re * dressed) * (sign τ.re * v τ)
    --     = sign σ.re * (sign τ.re * sign τ.re) * dressed * v τ
    --     = sign σ.re * 1 * dressed * v τ.
    have key : ((marshallSignS A σ.1).re * (marshallSignS A τ.1).re *
        dressedHeisenbergSReMatrix A J N σ.1 τ.1) *
        ((marshallSignS A τ.1).re * v τ) =
      (marshallSignS A σ.1).re *
        (((marshallSignS A τ.1).re * (marshallSignS A τ.1).re) *
          dressedHeisenbergSReMatrix A J N σ.1 τ.1 * v τ) := by ring
    rw [key, hsq_τ, one_mul]
  rw [Finset.sum_congr rfl (fun τ _ => hsum τ)]
  -- Now: ∑τ sign σ.re * (dressed_sec σ τ * v τ) = μ * (sign σ.re * v σ).
  rw [← Finset.mul_sum]
  -- ∑τ dressed_sec σ τ * v τ = dressed_sec.mulVec v σ.
  change (marshallSignS A σ.1).re *
      (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ =
    μ * ((marshallSignS A σ.1).re * v σ)
  rw [hσ]
  change (marshallSignS A σ.1).re * (μ * v σ) = μ * ((marshallSignS A σ.1).re * v σ)
  ring
end LatticeSystem.Quantum
