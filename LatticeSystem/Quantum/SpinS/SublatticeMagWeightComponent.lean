import LatticeSystem.Quantum.SpinS.SublatticeMagProjection
import LatticeSystem.Quantum.SpinS.SublatticeSpin

/-!
# Weight-component extraction for sublattice-Casimir eigenvectors

Scaffold for the sublattice Casimir spectral max bound (Issue #3658, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

Since `(Ŝ_A)²` commutes with `Ŝ_A^(3)`, it preserves each sublattice magnetization
subspace, so it commutes with the pointwise sublattice projector
(`SublatticeMagProjection.lean`).  Hence every non-zero `(Ŝ_A)²`-eigenvector has a
non-zero sublattice-weight component that is again a `(Ŝ_A)²`-eigenvector at the
same eigenvalue and lives in a single sublattice magnetization subspace.  This
reduces the sublattice Casimir bound to *weight* eigenvectors, on which the
highest-weight argument applies.

This is the sublattice analogue of `totalSpinSSquared_eigenvec_exists_weight_component`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- An operator commuting with `Ŝ_A^(3)` preserves each sublattice magnetization
subspace. -/
theorem mem_sublatticeMagSubspaceS_of_commute (A : Λ → Bool) (M : ℂ)
    (H : ManyBodyOpS Λ N) (hcomm : Commute (sublatticeSpinSOp3 N A) H)
    {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ sublatticeMagSubspaceS A M) :
    H.mulVec v ∈ sublatticeMagSubspaceS A M := by
  rw [mem_sublatticeMagSubspaceS_iff] at hv ⊢
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- `(Ŝ_A)²` preserves each sublattice magnetization subspace. -/
theorem sublatticeSpinSquaredS_mulVec_mem_sublatticeMagSubspaceS (A : Λ → Bool)
    (M : ℂ) {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ sublatticeMagSubspaceS A M) :
    (sublatticeSpinSquaredS N A).mulVec v ∈ sublatticeMagSubspaceS A M :=
  mem_sublatticeMagSubspaceS_of_commute A M _
    (sublatticeSpinSquaredS_commute_sublatticeSpinSOp3 N A).symm hv

/-- **Matrix-element vanishing for `(Ŝ_A)²`**: its off-sublattice-magnetization
matrix entries vanish, `(Ŝ_A)² σ τ = 0` whenever
`sublatticeMagEigenvalueS A σ ≠ sublatticeMagEigenvalueS A τ`. -/
theorem sublatticeSpinSquaredS_apply_eq_zero_of_sublatticeMagEigenvalueS_ne
    (A : Λ → Bool) {σ τ : Λ → Fin (N + 1)}
    (hne : sublatticeMagEigenvalueS A σ ≠ sublatticeMagEigenvalueS A τ) :
    (sublatticeSpinSquaredS N A) σ τ = 0 := by
  have hmem := sublatticeSpinSquaredS_mulVec_mem_sublatticeMagSubspaceS A
    (sublatticeMagEigenvalueS A τ) (basisVecS_mem_sublatticeMagSubspaceS A τ)
  have happ : (sublatticeSpinSquaredS N A).mulVec (basisVecS τ) σ =
      (sublatticeSpinSquaredS N A) σ τ := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single τ]
    · rw [basisVecS_self, mul_one]
    · intros ρ _ hρτ
      rw [basisVecS_of_ne hρτ, mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [← happ]
  exact sublatticeMagSubspaceS_apply_eq_zero_of_sublatticeMagEigenvalueS_ne A hmem hne

/-- **`(Ŝ_A)²` commutes with the sublattice projector**:
`(Ŝ_A)² · (sublatticeMagProjFn A M v) = sublatticeMagProjFn A M ((Ŝ_A)² · v)`. -/
theorem sublatticeSpinSquaredS_mulVec_sublatticeMagProjFn_eq (A : Λ → Bool) (M : ℂ)
    (v : (Λ → Fin (N + 1)) → ℂ) :
    (sublatticeSpinSquaredS N A).mulVec (sublatticeMagProjFn A M v) =
      sublatticeMagProjFn A M ((sublatticeSpinSquaredS N A).mulVec v) := by
  funext σ
  by_cases hσM : sublatticeMagEigenvalueS A σ = M
  · have hRHS : sublatticeMagProjFn A M ((sublatticeSpinSquaredS N A).mulVec v) σ =
        (sublatticeSpinSquaredS N A).mulVec v σ := by
      unfold sublatticeMagProjFn; simp [hσM]
    rw [hRHS, Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro τ _
    by_cases hτM : sublatticeMagEigenvalueS A τ = M
    · change (sublatticeSpinSquaredS N A) σ τ * sublatticeMagProjFn A M v τ =
        (sublatticeSpinSquaredS N A) σ τ * v τ
      unfold sublatticeMagProjFn; rw [if_pos hτM]
    · change (sublatticeSpinSquaredS N A) σ τ * sublatticeMagProjFn A M v τ =
        (sublatticeSpinSquaredS N A) σ τ * v τ
      have hne : sublatticeMagEigenvalueS A σ ≠ sublatticeMagEigenvalueS A τ := by
        rw [hσM]; exact Ne.symm hτM
      rw [sublatticeSpinSquaredS_apply_eq_zero_of_sublatticeMagEigenvalueS_ne A hne]
      ring
  · have hRHS : sublatticeMagProjFn A M ((sublatticeSpinSquaredS N A).mulVec v) σ = 0 := by
      unfold sublatticeMagProjFn; simp [hσM]
    rw [hRHS, Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro τ _
    by_cases hτM : sublatticeMagEigenvalueS A τ = M
    · have hne : sublatticeMagEigenvalueS A σ ≠ sublatticeMagEigenvalueS A τ := by
        rw [hτM]; exact hσM
      change (sublatticeSpinSquaredS N A) σ τ * sublatticeMagProjFn A M v τ = 0
      rw [sublatticeSpinSquaredS_apply_eq_zero_of_sublatticeMagEigenvalueS_ne A hne, zero_mul]
    · change (sublatticeSpinSquaredS N A) σ τ * sublatticeMagProjFn A M v τ = 0
      unfold sublatticeMagProjFn; rw [if_neg hτM, mul_zero]

/-- **Sublattice weight-component extraction**: a non-zero `(Ŝ_A)²`-eigenvector at
`γ` has a non-zero sublattice-weight component `sublatticeMagProjFn A (s_A − k) v`
(for some `k`) which is again a `(Ŝ_A)²`-eigenvector at `γ` and lies in the
sublattice magnetization subspace `sublatticeMagSubspaceS A (s_A − k)`. -/
theorem sublatticeSpinSquaredS_eigenvec_exists_weight_component (A : Λ → Bool)
    {γ : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hcas : (sublatticeSpinSquaredS N A).mulVec v = γ • v) :
    ∃ k : Fin ((Finset.univ.filter (fun x : Λ => A x = true)).card * N + 1),
      sublatticeMagProjFn A
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
            (k.val : ℂ)) v ≠ 0 ∧
      (sublatticeSpinSquaredS N A).mulVec
          (sublatticeMagProjFn A
            (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
              (k.val : ℂ)) v) =
        γ • sublatticeMagProjFn A
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
            (k.val : ℂ)) v ∧
      sublatticeMagProjFn A
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
            (k.val : ℂ)) v ∈
        sublatticeMagSubspaceS A
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
            (k.val : ℂ)) := by
  classical
  have hsum_ne :
      (∑ k : Fin ((Finset.univ.filter (fun x : Λ => A x = true)).card * N + 1),
        sublatticeMagProjFn A
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
            (k.val : ℂ)) v) ≠ 0 := by
    rw [sum_sublatticeMagProjFn_eq A v]; exact hv
  obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  refine ⟨k, hk, ?_, sublatticeMagProjFn_mem_sublatticeMagSubspaceS A _ v⟩
  rw [sublatticeSpinSquaredS_mulVec_sublatticeMagProjFn_eq, hcas, sublatticeMagProjFn_smul]

end LatticeSystem.Quantum
