import LatticeSystem.Quantum.SpinS.SublatticeSzBound

/-!
# Sublattice magnetization grading

Scaffold for the sublattice Casimir spectral max bound (Issue #3658, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

To run the highest-weight argument bounding `(Ŝ_A)² ⪯ s_A(s_A+1)·1`, we mirror
the total magnetization grading by `Ŝ_tot^(3)` (`Magnetization.lean`) for the
*sublattice* operator `Ŝ_A^(3) = ∑_{x ∈ A} Ŝ_x^(3)`.

`Ŝ_A^(3)` is diagonal in the basis with eigenvalue
`m_A(σ) = ∑_{x ∈ A} (N/2 − σ_x)` (`sublatticeSpinSOp3_mulVec_basisVecS`).  We
package this as `sublatticeMagEigenvalueS A σ` and define the sublattice
magnetization subspaces `sublatticeMagSubspaceS A M` as its eigenspaces, with the
basic submodule API mirroring `magSubspaceS`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The sublattice magnetic-quantum-number eigenvalue of `Ŝ_A^(3)` on the basis
state `|σ⟩`:

  `sublatticeMagEigenvalueS A σ := ∑_{x ∈ A} (N/2 − σ_x)`. -/
noncomputable def sublatticeMagEigenvalueS (A : Λ → Bool) (σ : Λ → Fin (N + 1)) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : Λ => A x = true),
    ((N : ℂ) / 2 - ((σ x).val : ℂ))

omit [DecidableEq Λ] in
/-- Definitional unfolding of `sublatticeMagEigenvalueS`. -/
theorem sublatticeMagEigenvalueS_def (A : Λ → Bool) (σ : Λ → Fin (N + 1)) :
    sublatticeMagEigenvalueS A σ =
      ∑ x ∈ Finset.univ.filter (fun x : Λ => A x = true),
        ((N : ℂ) / 2 - ((σ x).val : ℂ)) := rfl

/-- The sublattice magnetization subspace `sublatticeMagSubspaceS A M`: the
`Ŝ_A^(3)`-eigenspace with eigenvalue `M`. -/
noncomputable def sublatticeMagSubspaceS (A : Λ → Bool) (M : ℂ) :
    Submodule ℂ ((Λ → Fin (N + 1)) → ℂ) where
  carrier := { v | (sublatticeSpinSOp3 N A).mulVec v = M • v }
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.mulVec_zero, smul_zero]
  add_mem' := by
    intros v w hv hw
    simp only [Set.mem_setOf_eq] at hv hw ⊢
    rw [Matrix.mulVec_add, hv, hw, smul_add]
  smul_mem' := by
    intros c v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [Matrix.mulVec_smul, hv, smul_comm]

/-- A vector lies in `sublatticeMagSubspaceS A M` iff it is a `Ŝ_A^(3)`
eigenvector with eigenvalue `M`. -/
@[simp]
theorem mem_sublatticeMagSubspaceS_iff (A : Λ → Bool) (M : ℂ)
    (v : (Λ → Fin (N + 1)) → ℂ) :
    v ∈ sublatticeMagSubspaceS A M ↔ (sublatticeSpinSOp3 N A).mulVec v = M • v :=
  Iff.rfl

/-- Distinct sublattice magnetization eigenvalues give disjoint subspaces. -/
theorem sublatticeMagSubspaceS_disjoint (A : Λ → Bool) {M M' : ℂ} (hMM' : M ≠ M') :
    Disjoint (sublatticeMagSubspaceS (N := N) A M)
      (sublatticeMagSubspaceS (N := N) A M') := by
  rw [Submodule.disjoint_def]
  intros v hM hM'
  rw [mem_sublatticeMagSubspaceS_iff] at hM hM'
  have heq : M • v = M' • v := hM.symm.trans hM'
  have hsub : (M - M') • v = 0 := by
    rw [sub_smul, heq, sub_self]
  have hne : M - M' ≠ 0 := sub_ne_zero.mpr hMM'
  exact (smul_eq_zero.mp hsub).resolve_left hne

/-- Each basis state `|σ⟩` lies in the sublattice magnetization subspace at its
own eigenvalue `sublatticeMagEigenvalueS A σ`. -/
theorem basisVecS_mem_sublatticeMagSubspaceS (A : Λ → Bool) (σ : Λ → Fin (N + 1)) :
    (basisVecS σ : (Λ → Fin (N + 1)) → ℂ) ∈
      sublatticeMagSubspaceS A (sublatticeMagEigenvalueS A σ) :=
  sublatticeSpinSOp3_mulVec_basisVecS A σ

end LatticeSystem.Quantum
