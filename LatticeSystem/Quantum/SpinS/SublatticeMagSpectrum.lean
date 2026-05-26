import LatticeSystem.Quantum.SpinS.SublatticeMagnetization

/-!
# Sublattice magnetization spectrum

Scaffold for the sublattice Casimir spectral max bound (Issue #3658, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

`Ŝ_A^(3)` is diagonal in the basis with diagonal entry `sublatticeMagEigenvalueS A σ`
(`SublatticeMagnetization.lean`).  Consequently a sublattice magnetization
eigenvalue `M` outside the diagonal spectrum gives a trivial eigenspace
`sublatticeMagSubspaceS A M = ⊥`.  This is the sublattice analogue of
`totalSpinSOp3_apply_diag/off_diag` and `magSubspaceS_eq_bot_of_not_in_spectrum`,
and lets the highest-weight argument for `(Ŝ_A)²` conclude that any attained
sublattice magnetization is an actual basis eigenvalue (hence `|M| ≤ s_A`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The matrix entry of `Ŝ_A^(3)`: `sublatticeMagEigenvalueS A σ` on the diagonal,
zero off-diagonal. -/
theorem sublatticeSpinSOp3_apply (A : Λ → Bool) (σ' σ : Λ → Fin (N + 1)) :
    (sublatticeSpinSOp3 N A) σ' σ =
      sublatticeMagEigenvalueS A σ * (if σ' = σ then 1 else 0) := by
  classical
  have hkey := sublatticeSpinSOp3_mulVec_basisVecS A σ
  have happly :
      (sublatticeSpinSOp3 N A).mulVec (basisVecS σ) σ' =
        (sublatticeSpinSOp3 N A) σ' σ := by
    change ∑ τ, (sublatticeSpinSOp3 N A) σ' τ * basisVecS σ τ =
      (sublatticeSpinSOp3 N A) σ' σ
    simp_rw [basisVecS_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ σ
        (fun τ => (sublatticeSpinSOp3 N A) σ' τ)]
    simp
  have heq : (sublatticeSpinSOp3 N A).mulVec (basisVecS σ) σ' =
      sublatticeMagEigenvalueS A σ * basisVecS σ σ' := by
    rw [hkey, Pi.smul_apply, smul_eq_mul, sublatticeMagEigenvalueS_def]
  rw [happly] at heq
  rw [heq, basisVecS_apply]

/-- The diagonal entry of `Ŝ_A^(3)` is `sublatticeMagEigenvalueS A σ`. -/
theorem sublatticeSpinSOp3_apply_diag (A : Λ → Bool) (σ : Λ → Fin (N + 1)) :
    (sublatticeSpinSOp3 N A) σ σ = sublatticeMagEigenvalueS A σ := by
  rw [sublatticeSpinSOp3_apply, if_pos rfl, mul_one]

/-- Off-diagonal entries of `Ŝ_A^(3)` vanish. -/
theorem sublatticeSpinSOp3_apply_off_diag (A : Λ → Bool) {σ' σ : Λ → Fin (N + 1)}
    (h : σ' ≠ σ) :
    (sublatticeSpinSOp3 N A) σ' σ = 0 := by
  rw [sublatticeSpinSOp3_apply, if_neg h, mul_zero]

/-- **Out-of-spectrum sublattice eigenspace is trivial**: if `M` is not the
sublattice magnetization eigenvalue `sublatticeMagEigenvalueS A σ` of any basis
state `σ`, then `sublatticeMagSubspaceS A M = ⊥`. -/
theorem sublatticeMagSubspaceS_eq_bot_of_not_in_spectrum (A : Λ → Bool) {M : ℂ}
    (hM : ∀ σ : Λ → Fin (N + 1), sublatticeMagEigenvalueS A σ ≠ M) :
    sublatticeMagSubspaceS (N := N) A M = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [mem_sublatticeMagSubspaceS_iff] at hv
  funext τ
  have hτ_lhs : (sublatticeSpinSOp3 N A).mulVec v τ =
      sublatticeMagEigenvalueS A τ * v τ := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single τ]
    · rw [sublatticeSpinSOp3_apply_diag]
    · intros σ _ hστ
      rw [sublatticeSpinSOp3_apply_off_diag A (Ne.symm hστ), zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hτ_rhs : (M • v) τ = M * v τ := by
    simp [Pi.smul_apply, smul_eq_mul]
  have hτ_eq : sublatticeMagEigenvalueS A τ * v τ = M * v τ := by
    rw [← hτ_lhs, hv, hτ_rhs]
  have hsub : (sublatticeMagEigenvalueS A τ - M) * v τ = 0 := by
    rw [sub_mul, hτ_eq, sub_self]
  have hne : sublatticeMagEigenvalueS A τ - M ≠ 0 := sub_ne_zero.mpr (hM τ)
  exact (mul_eq_zero.mp hsub).resolve_left hne

end LatticeSystem.Quantum
