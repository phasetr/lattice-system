import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Spin-`S` magnetization function on configurations
(Tasaki §2.5 Phase B-β β-4a)

For a spin parameter `N : ℕ` (with `N = 2S`) and a finite lattice `Λ`,
each configuration `σ : Λ → Fin (N + 1)` carries a **magnetization**
quantum number. We use the natural-number index sum

  `magSumS σ := Σ_{x : Λ} (σ x).val`

as the basic combinatorial quantity. The physical magnetic quantum
number is `(|Λ| · N / 2) − magSumS σ` (in units of `S`).

The magnetic-quantum-number range of `magSumS` is
`{0, 1, ..., |Λ| · N}`.

For spin-1/2 (`N = 1`), `magSumS σ = |{x : σ x = 1}|` is the
"down-spin count" and matches the existing spin-1/2 magnetization
encoding (`Quantum/MagnetizationSubspace.lean`).

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The magnetization-index sum of a spin-`S` configuration. -/
def magSumS (σ : Λ → Fin (N + 1)) : ℕ :=
  ∑ x : Λ, (σ x).val

omit [DecidableEq Λ] in
/-- `magSumS σ ≤ |Λ| · N`. -/
theorem magSumS_le (σ : Λ → Fin (N + 1)) :
    magSumS σ ≤ Fintype.card Λ * N := by
  unfold magSumS
  calc ∑ x : Λ, (σ x).val
      ≤ ∑ _ : Λ, N := by
        refine Finset.sum_le_sum ?_
        intro x _
        have := (σ x).isLt
        omega
    _ = Fintype.card Λ * N := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-! ## Magnetization subspace -/

/-- The magnetization-`M` subspace of the multi-site spin-`S` Hilbert
space: the `Ŝ_tot^{(3)}`-eigenspace for eigenvalue `M`, packaged as a
`Submodule ℂ`. -/
noncomputable def magSubspaceS (Λ : Type*) [Fintype Λ] [DecidableEq Λ]
    (N : ℕ) (M : ℂ) :
    Submodule ℂ ((Λ → Fin (N + 1)) → ℂ) where
  carrier := { v | (totalSpinSOp3 Λ N).mulVec v = M • v }
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

/-- A vector lies in `magSubspaceS Λ N M` iff it is a `Ŝ_tot^{(3)}`
eigenvector with eigenvalue `M`. -/
@[simp]
theorem mem_magSubspaceS_iff (M : ℂ) (v : (Λ → Fin (N + 1)) → ℂ) :
    v ∈ magSubspaceS Λ N M ↔ (totalSpinSOp3 Λ N).mulVec v = M • v :=
  Iff.rfl

/-- Distinct magnetization eigenvalues give disjoint subspaces. -/
theorem magSubspaceS_disjoint {M M' : ℂ} (hMM' : M ≠ M') :
    Disjoint (magSubspaceS Λ N M) (magSubspaceS Λ N M') := by
  rw [Submodule.disjoint_def]
  intros v hM hM'
  rw [mem_magSubspaceS_iff] at hM hM'
  have heq : M • v = M' • v := hM.symm.trans hM'
  have hsub : (M - M') • v = 0 := by
    rw [sub_smul, heq, sub_self]
  have hne : M - M' ≠ 0 := sub_ne_zero.mpr hMM'
  exact (smul_eq_zero.mp hsub).resolve_left hne

/-- The magnetic-quantum-number eigenvalue of `Ŝ_tot^{(3)}` on the
basis state `|σ⟩`:

  `magEigenvalueS σ := (|Λ| · N : ℂ)/2 − magSumS σ`. -/
noncomputable def magEigenvalueS (σ : Λ → Fin (N + 1)) : ℂ :=
  ((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (magSumS σ : ℂ)

/-- `onSiteS x (spinSOp3 N) · |σ⟩ = ((N : ℂ)/2 − (σ x).val) • |σ⟩`. -/
theorem onSiteS_spinSOp3_mulVec_basisVecS (x : Λ) (σ : Λ → Fin (N + 1)) :
    (onSiteS x (spinSOp3 N) : ManyBodyOpS Λ N).mulVec (basisVecS σ) =
      ((N : ℂ) / 2 - (σ x).val) • basisVecS σ := by
  funext τ
  show ∑ τ', (onSiteS x (spinSOp3 N)) τ τ' * basisVecS σ τ' =
       ((N : ℂ) / 2 - (σ x).val) * basisVecS σ τ
  rw [Fintype.sum_eq_single σ (fun ρ hρ => by
    simp only [basisVecS, if_neg hρ, mul_zero])]
  -- Goal: (onSiteS x (spinSOp3 N)) τ σ * basisVecS σ σ = ((N : ℂ) / 2 - σ x.val) * basisVecS σ τ.
  rw [basisVecS_self, mul_one]
  by_cases heq : τ = σ
  · -- τ = σ: LHS = (spinSOp3 N) (σ x) (σ x) = (N/2 - σ x.val).
    rw [heq, basisVecS_self, mul_one]
    rw [onSiteS_apply, if_pos (fun _ _ => rfl)]
    change (Matrix.diagonal fun k => ((N : ℂ) / 2 - (k.val : ℂ))) (σ x) (σ x) =
        (N : ℂ) / 2 - ((σ x).val : ℂ)
    rw [Matrix.diagonal_apply_eq]
  · rw [basisVecS_of_ne heq, mul_zero]
    -- LHS = (onSiteS x (spinSOp3 N)) τ σ. We show this is 0 when τ ≠ σ.
    rw [onSiteS_apply]
    by_cases hagree : ∀ k, k ≠ x → τ k = σ k
    · rw [if_pos hagree]
      have hτx : τ x ≠ σ x := by
        intro hτx
        apply heq
        funext k
        by_cases hkx : k = x
        · subst hkx; exact hτx
        · exact hagree k hkx
      change (Matrix.diagonal fun k => ((N : ℂ) / 2 - (k.val : ℂ))) (τ x) (σ x) = 0
      rw [Matrix.diagonal_apply_ne _ hτx]
    · rw [if_neg hagree]

end LatticeSystem.Quantum
