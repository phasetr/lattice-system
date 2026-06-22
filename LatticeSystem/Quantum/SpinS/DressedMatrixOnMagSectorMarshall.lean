import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshallCore

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
end LatticeSystem.Quantum
