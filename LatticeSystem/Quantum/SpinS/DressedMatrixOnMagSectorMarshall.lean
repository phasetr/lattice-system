import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSector

/-!
# Heisenberg sector matrix via Marshall reverse + inverse Marshall
conjugation uniqueness (build-speed companion)

Build-speed companion to `DressedMatrixOnMagSector.lean`. Hosts
the trailing sections "Heisenberg sector matrix and its eigenvector
via Marshall reverse" and "Inverse Marshall conjugation and
uniqueness on the Heisenberg sector" through the final
`marshallLiebMattis_spinS_heisenbergSector_groundState`
(originally lines 370..868 of the pre-#40 parent file).

Splitting these blocks out drops the parent from ~868 lines to
~369 lines.

`MagSectorEmbedding.lean` updated to additionally import this
companion.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body
  Systems*, Springer 2020, §2.5 Theorem 2.2 (Marshall–Lieb–Mattis),
  pp. 39–43.
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

Combined with `exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector`
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

/-- **Spin-S Marshall–Lieb–Mattis ground state on the original Heisenberg
sector matrix** (γ-3 FINAL THEOREM, Heisenberg form): there exists a
NON-ZERO real eigenvector of the (un-dressed) Heisenberg sector matrix
with eigenvalue `μ < c` and the Marshall sign structure
`w τ = (marshallSignS A τ.1).re * (positive function of τ)`.

Composition of:
- `exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector`
  (#850, γ-3 dressed-form): ∃ μ < c, ∃ v > 0, dressed_sec.mulVec v = μ • v.
- `heisenbergHamiltonianSReMatrixOnMagSector_mulVec_of_dressed_eigenvec`
  (Marshall-conjugation, this PR).

The eigenvector `w τ := sign A τ.1 .re * v τ` has `|w τ| = v τ > 0`,
so `w` is everywhere non-zero. The sign of `w` matches the Marshall sign
structure. This is the ground-state half of Tasaki §2.5 Theorem 2.2 in
the magnetization sector. -/
theorem exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
        μ • (fun σ => (marshallSignS A σ.1).re * v σ) := by
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_positive_eigenvector_dressedHeisenbergSReMatrixOnMagSector
      (M := M) A N c
      hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
  exact ⟨μ, v, hμ, hv_pos,
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
      A N hJ_real hmul⟩

/-! ## Inverse Marshall conjugation and uniqueness on the Heisenberg sector -/

/-- **Inverse Marshall conjugation** (heisenberg → dressed): given an
eigenvector `w` of the (un-dressed) Heisenberg sector matrix with
eigenvalue `μ`, the Marshall-conjugated vector `sign · w` is an
eigenvector of the dressed Heisenberg sector matrix with the same
eigenvalue `μ`.

Symmetric to `heisenbergHamiltonianSReMatrixOnMagSector_mulVec_of_dressed_eigenvec`,
using the OTHER direction of the matrix relation
`dressed = sign · sign · heis`. -/
theorem dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    {μ : ℝ} {w : magConfigS V N M → ℝ}
    (hw : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ • w) :
    (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec
      (fun σ => (marshallSignS A σ.1).re * w σ) =
      μ • (fun σ => (marshallSignS A σ.1).re * w σ) := by
  funext σ
  have hσ := congrFun hw σ
  change (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec
      (fun τ => (marshallSignS A τ.1).re * w τ) σ =
    μ * ((marshallSignS A σ.1).re * w σ)
  change ∑ τ, dressedHeisenbergSReMatrixOnMagSector A J N M σ τ *
      ((marshallSignS A τ.1).re * w τ) =
    μ * ((marshallSignS A σ.1).re * w σ)
  have hsum : ∀ τ : magConfigS V N M,
      dressedHeisenbergSReMatrixOnMagSector A J N M σ τ *
        ((marshallSignS A τ.1).re * w τ) =
      (marshallSignS A σ.1).re *
        (heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ * w τ) := by
    intro τ
    rw [dressedHeisenbergSReMatrixOnMagSector_apply,
      heisenbergHamiltonianSReMatrixOnMagSector_apply,
      dressedHeisenbergSReMatrix_eq_marshallSign_mul_heisenberg A N hJ_real]
    have hsq_τ : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    have key : ((marshallSignS A σ.1).re * (marshallSignS A τ.1).re *
        heisenbergHamiltonianSReMatrix J N σ.1 τ.1) *
        ((marshallSignS A τ.1).re * w τ) =
      (marshallSignS A σ.1).re *
        (((marshallSignS A τ.1).re * (marshallSignS A τ.1).re) *
          heisenbergHamiltonianSReMatrix J N σ.1 τ.1 * w τ) := by ring
    rw [key, hsq_τ, one_mul]
  rw [Finset.sum_congr rfl (fun τ _ => hsum τ)]
  rw [← Finset.mul_sum]
  change (marshallSignS A σ.1).re *
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w σ =
    μ * ((marshallSignS A σ.1).re * w σ)
  rw [hσ]
  change (marshallSignS A σ.1).re * (μ * w σ) = μ * ((marshallSignS A σ.1).re * w σ)
  ring

/-- Convert an eigenvector of the dressed matrix to an eigenvector of
the shifted matrix (with shifted eigenvalue): if `dressed_sec v = μ v`,
then `shifted_sec v = (c − μ) v`. (Inverse of #849.) -/
theorem shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) {M : ℕ}
    {μ : ℝ} {v : magConfigS V N M → ℝ}
    (hv : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ • v) :
    (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = (c - μ) • v := by
  -- shifted = c • 1 - dressed.
  have hdef := shiftedDressedSReMatrixOnMagSector_eq_smul_sub_dressed A J N c M
  rw [hdef]
  -- Goal: (c • 1 - dressed).mulVec v = (c - μ) • v.
  funext σ
  rw [Matrix.sub_mulVec]
  change (c • (1 : Matrix _ _ ℝ)).mulVec v σ -
      (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ =
    (c - μ) * v σ
  rw [show ((c : ℝ) • (1 : Matrix _ _ ℝ)).mulVec v =
      c • (1 : Matrix _ _ ℝ).mulVec v from Matrix.smul_mulVec _ _ _,
    Matrix.one_mulVec]
  have hσ := congrFun hv σ
  change c * v σ - (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v σ =
    (c - μ) * v σ
  have : (μ • v) σ = μ * v σ := rfl
  rw [this] at hσ
  linarith

/-- **Uniqueness of dressed sector eigenvectors at a given eigenvalue**:
any two strictly positive eigenvectors of the dressed Heisenberg sector
matrix with the same eigenvalue `μ` are positive scalar multiples of
each other.

Reduction to `pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector`
(#848): convert both `dressed_sec`-eigenvectors to `shifted_sec`-
eigenvectors at the shifted eigenvalue `c - μ`, then apply PF
uniqueness on the shifted matrix. -/
theorem pos_eigenvec_unique_dressedHeisenbergSReMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec w = μ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    ∃ r : ℝ, 0 < r ∧ w = r • v := by
  -- Convert both to shifted-eigenvectors at (c - μ).
  have hv' := shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
    A J N c hv
  have hw' := shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec
    A J N c hw
  exact pos_eigenvec_unique_shiftedDressedSReMatrixOnMagSector A N c
    hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
    hv' hv_pos hw' hw_pos

/-- **Uniqueness of Marshall-positive Heisenberg sector eigenvectors**
(Tasaki §2.5 Theorem 2.2 nondegeneracy half, Heisenberg form): any two
real eigenvectors `w₁, w₂` of the (un-dressed) Heisenberg sector matrix
at the SAME eigenvalue `μ`, both with strictly positive Marshall-
conjugates `sign · wᵢ > 0`, are positive scalar multiples of each
other.

Reduction: by inverse Marshall conjugation, the conjugates `vᵢ := sign · wᵢ`
are positive eigenvectors of the dressed sector matrix at `μ`. By dressed
sector uniqueness (this PR) `v₂ = r • v₁` for some `r > 0`. Multiplying
both sides by `sign` (which squares to 1) gives `w₂ = r • w₁`. -/
theorem marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {w₁ w₂ : magConfigS V N M → ℝ}
    (hw₁ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₁ = μ • w₁)
    (hw₁_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₁ σ)
    (hw₂ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₂ = μ • w₂)
    (hw₂_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₂ σ) :
    ∃ r : ℝ, 0 < r ∧ w₂ = r • w₁ := by
  -- Marshall-conjugate both: vᵢ := sign · wᵢ are dressed eigenvectors.
  have hv₁ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    A N hJ_real hw₁
  have hv₂ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    A N hJ_real hw₂
  -- Apply dressed uniqueness.
  obtain ⟨r, hr_pos, hrel⟩ :=
    pos_eigenvec_unique_dressedHeisenbergSReMatrixOnMagSector
      A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
      hv₁ hw₁_marshall_pos hv₂ hw₂_marshall_pos
  -- hrel : (fun σ => sign σ.1.re * w₂ σ) = r • (fun σ => sign σ.1.re * w₁ σ).
  refine ⟨r, hr_pos, ?_⟩
  funext σ
  -- Multiply both sides of hrel σ by sign σ.1.re; sign² = 1 cancels.
  have hσ := congrFun hrel σ
  -- hσ : sign σ.1.re * w₂ σ = r * (sign σ.1.re * w₁ σ).
  change (marshallSignS A σ.1).re * w₂ σ =
    r * ((marshallSignS A σ.1).re * w₁ σ) at hσ
  have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
    marshallSignS_re_sq A σ.1
  -- Multiply both sides by sign σ.1.re.
  have h_eq : (marshallSignS A σ.1).re *
      ((marshallSignS A σ.1).re * w₂ σ) =
    (marshallSignS A σ.1).re *
      (r * ((marshallSignS A σ.1).re * w₁ σ)) := by
    rw [hσ]
  -- Simplify both sides via sign² = 1.
  change w₂ σ = r * w₁ σ
  have lhs_eq : (marshallSignS A σ.1).re *
      ((marshallSignS A σ.1).re * w₂ σ) = w₂ σ := by
    rw [← mul_assoc, hsq, one_mul]
  have rhs_eq : (marshallSignS A σ.1).re *
      (r * ((marshallSignS A σ.1).re * w₁ σ)) = r * w₁ σ := by
    have : (marshallSignS A σ.1).re *
        (r * ((marshallSignS A σ.1).re * w₁ σ)) =
      ((marshallSignS A σ.1).re * (marshallSignS A σ.1).re) * (r * w₁ σ) := by
      ring
    rw [this, hsq, one_mul]
  linarith

/-- **Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis), ground-state form
on the magnetization sector**: for the bipartite antiferromagnetic
Heisenberg matrix restricted to the magnetization-`M` sector, there
exists a Marshall-positive ground-state eigenvector `sign · v` (with
`v > 0` componentwise) at some eigenvalue `μ < c`, AND any other
Marshall-positive eigenvector at the SAME eigenvalue `μ` is a positive
scalar multiple of it.

Bundles the existence theorem
(`exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector`,
PR #853) with the same-eigenvalue uniqueness theorem
(`marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector`,
PR #854) into the form most directly usable downstream. -/
theorem marshallLiebMattis_spinS_heisenbergSector_groundState
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧
      (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * v σ) =
        μ • (fun σ => (marshallSignS A σ.1).re * v σ) ∧
      (∀ {w : magConfigS V N M → ℝ},
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ • w →
        (∀ σ, 0 < (marshallSignS A σ.1).re * w σ) →
        ∃ r : ℝ, 0 < r ∧
          w = r • (fun σ => (marshallSignS A σ.1).re * v σ)) := by
  obtain ⟨μ, v, hμ_lt, hv_pos, hmul⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
      (M := M) A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate
  refine ⟨μ, v, hμ_lt, hv_pos, hmul, ?_⟩
  intro w hw hw_pos
  have hsign_v_pos : ∀ σ, 0 < (marshallSignS A σ.1).re *
      ((marshallSignS A σ.1).re * v σ) := fun σ => by
    have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
      marshallSignS_re_sq A σ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hv_pos σ
  exact marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector
    A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
    hmul hsign_v_pos hw hw_pos



end LatticeSystem.Quantum
