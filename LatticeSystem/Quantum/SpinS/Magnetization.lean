import LatticeSystem.Quantum.SpinS.ConfigCombinatorics
import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Spin-`S` magnetization operator and its eigenspaces
(Tasaki §2.5 Phase B-β β-4a)

The matrix-level magnetization layer for a spin parameter `N : ℕ`
(with `N = 2S`) on a finite lattice `Λ`.  The combinatorial index sum
`magSumS σ = Σ_{x : Λ} (σ x).val` of a configuration `σ : Λ → Fin (N + 1)`
is supplied by `LatticeSystem/Quantum/SpinS/ConfigCombinatorics.lean`;
here it is turned into the `Ŝ_tot^{(3)}` eigenvalue

  `magEigenvalueS σ := (|Λ| · N / 2) − magSumS σ`

(the physical magnetic quantum number, in units of `S`), and the
eigenspaces `magSubspaceS Λ N M` are shown to be pairwise disjoint, to
contain every basis state `|σ⟩`, and to span the whole multi-site
Hilbert space.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

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

omit [DecidableEq Λ] in
/-- Definitional unfolding of `magEigenvalueS`. -/
theorem magEigenvalueS_def (σ : Λ → Fin (N + 1)) :
    magEigenvalueS σ =
      ((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (magSumS σ : ℂ) := rfl

/-- `onSiteS x (spinSOp3 N) · |σ⟩ = ((N : ℂ)/2 − (σ x).val) • |σ⟩`. -/
theorem onSiteS_spinSOp3_mulVec_basisVecS (x : Λ) (σ : Λ → Fin (N + 1)) :
    (onSiteS x (spinSOp3 N) : ManyBodyOpS Λ N).mulVec (basisVecS σ) =
      ((N : ℂ) / 2 - (σ x).val) • basisVecS σ := by
  funext τ
  change ∑ τ', (onSiteS x (spinSOp3 N)) τ τ' * basisVecS σ τ' =
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

/-- `Ŝ_tot^{(3)} · |σ⟩ = magEigenvalueS σ • |σ⟩` — every basis state
is a `Ŝ_tot^{(3)}`-eigenvector. -/
theorem totalSpinSOp3_mulVec_basisVecS (σ : Λ → Fin (N + 1)) :
    (totalSpinSOp3 Λ N).mulVec (basisVecS σ) =
      magEigenvalueS σ • basisVecS σ := by
  unfold totalSpinSOp3
  -- Distribute mulVec over the Finset.sum:
  have hsum : (∑ x : Λ, onSiteS x (spinSOp3 N) : ManyBodyOpS Λ N).mulVec
        (basisVecS σ) =
      ∑ x : Λ, (onSiteS x (spinSOp3 N) : ManyBodyOpS Λ N).mulVec
        (basisVecS σ) := by
    classical
    induction (Finset.univ : Finset Λ) using Finset.induction_on with
    | empty => simp
    | @insert a t hat ih =>
      rw [Finset.sum_insert hat, Finset.sum_insert hat,
          Matrix.add_mulVec, ih]
  rw [hsum]
  simp_rw [onSiteS_spinSOp3_mulVec_basisVecS]
  rw [← Finset.sum_smul]
  congr 1
  unfold magEigenvalueS magSumS
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_univ]
  push_cast
  rw [nsmul_eq_mul]
  ring

/-- Every basis state lies in the magnetization-`magEigenvalueS σ` subspace. -/
theorem basisVecS_mem_magSubspaceS (σ : Λ → Fin (N + 1)) :
    (basisVecS σ : (Λ → Fin (N + 1)) → ℂ) ∈
      magSubspaceS Λ N (magEigenvalueS σ) :=
  totalSpinSOp3_mulVec_basisVecS σ

/-- An operator that commutes with `Ŝ_tot^{(3)}` preserves each
magnetization subspace. -/
theorem mem_magSubspaceS_of_commute (M : ℂ) (H : ManyBodyOpS Λ N)
    (hcomm : Commute (totalSpinSOp3 Λ N) H)
    {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ magSubspaceS Λ N M) :
    H.mulVec v ∈ magSubspaceS Λ N M := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]

/-- General matrix entry of `Ŝ_tot^{(3)}` extracted via the eigenvalue
equation `S^z |σ⟩ = magEig σ • |σ⟩` evaluated at row `σ'`. -/
theorem totalSpinSOp3_apply (σ' σ : Λ → Fin (N + 1)) :
    (totalSpinSOp3 Λ N) σ' σ =
      magEigenvalueS σ * (if σ' = σ then 1 else 0) := by
  classical
  have hkey := totalSpinSOp3_mulVec_basisVecS σ
  have happly :
      (totalSpinSOp3 Λ N).mulVec (basisVecS σ) σ' =
        (totalSpinSOp3 Λ N) σ' σ := by
    change ∑ τ, (totalSpinSOp3 Λ N) σ' τ * basisVecS σ τ =
      (totalSpinSOp3 Λ N) σ' σ
    simp_rw [basisVecS_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ σ
        (fun τ => (totalSpinSOp3 Λ N) σ' τ)]
    simp
  have heq : (totalSpinSOp3 Λ N).mulVec (basisVecS σ) σ' =
      magEigenvalueS σ * basisVecS σ σ' := by
    rw [hkey, Pi.smul_apply, smul_eq_mul]
  rw [happly] at heq
  rw [heq, basisVecS_apply]

/-- The diagonal entry of `Ŝ_tot^{(3)}` is `magEigenvalueS σ`. -/
theorem totalSpinSOp3_apply_diag (σ : Λ → Fin (N + 1)) :
    (totalSpinSOp3 Λ N) σ σ = magEigenvalueS σ := by
  rw [totalSpinSOp3_apply, if_pos rfl, mul_one]

/-- Off-diagonal entries of `Ŝ_tot^{(3)}` vanish. -/
theorem totalSpinSOp3_apply_off_diag {σ' σ : Λ → Fin (N + 1)}
    (h : σ' ≠ σ) :
    (totalSpinSOp3 Λ N) σ' σ = 0 := by
  rw [totalSpinSOp3_apply, if_neg h, mul_zero]

/-- Every basis state lies in the supremum of all magnetization
subspaces. This is a stepping stone toward proving that the
magnetization subspaces span the full multi-site Hilbert space. -/
theorem basisVecS_mem_iSup_magSubspaceS (σ : Λ → Fin (N + 1)) :
    (basisVecS σ : (Λ → Fin (N + 1)) → ℂ) ∈
      ⨆ M : ℂ, magSubspaceS Λ N M :=
  Submodule.mem_iSup_of_mem (magEigenvalueS σ) (basisVecS_mem_magSubspaceS σ)

/-- **Basis decomposition** of any vector: `v = Σ_σ v(σ) • |σ⟩`.
This is the standard expansion of a function on a finite set into
indicator functions. -/
theorem fun_eq_sum_smul_basisVecS (v : (Λ → Fin (N + 1)) → ℂ) :
    v = ∑ σ : Λ → Fin (N + 1), v σ • (basisVecS σ : (Λ → Fin (N + 1)) → ℂ) := by
  funext τ
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, basisVecS_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ τ (fun σ => v σ)]
  simp

/-- **Magnetization-subspace decomposition is total**: every vector
in the multi-site spin-`S` Hilbert space lies in the supremum of all
magnetization subspaces. Equivalently, `⨆_M magSubspaceS Λ N M = ⊤`. -/
theorem iSup_magSubspaceS_eq_top :
    (⨆ M : ℂ, magSubspaceS Λ N M) = ⊤ := by
  refine eq_top_iff.mpr (fun v _ => ?_)
  rw [fun_eq_sum_smul_basisVecS v]
  refine Submodule.sum_mem _ ?_
  intro σ _
  exact (⨆ M : ℂ, magSubspaceS Λ N M).smul_mem _ (basisVecS_mem_iSup_magSubspaceS σ)

/-! ## Constant configurations -/

omit [DecidableEq Λ] in
/-- `magEigenvalueS σ ∈ ℝ`: the eigenvalue is real-valued (its
imaginary part is zero). The eigenvalue is constructed as
`(|Λ| · N : ℂ)/2 - magSumS σ`, both terms real. -/
theorem magEigenvalueS_im_zero (σ : Λ → Fin (N + 1)) :
    (magEigenvalueS σ).im = 0 := by
  unfold magEigenvalueS
  simp

omit [DecidableEq Λ] in
/-- The real part of `magEigenvalueS σ` is `(|Λ| · N : ℝ)/2 - magSumS σ`. -/
theorem magEigenvalueS_re (σ : Λ → Fin (N + 1)) :
    (magEigenvalueS σ).re =
      ((Fintype.card Λ : ℝ) * (N : ℝ)) / 2 - (magSumS σ : ℝ) := by
  unfold magEigenvalueS
  simp

omit [DecidableEq Λ] in
/-- `magEigenvalueS σ = ((magEigenvalueS σ).re : ℂ)`: its imaginary
part vanishes, so it equals its embedded real part. -/
theorem magEigenvalueS_eq_ofReal_re (σ : Λ → Fin (N + 1)) :
    magEigenvalueS σ = ((magEigenvalueS σ).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [magEigenvalueS_im_zero]

omit [DecidableEq Λ] in
/-- `magEigenvalueS σ = magEigenvalueS σ' ↔ magSumS σ = magSumS σ'`:
two configurations have the same eigenvalue iff they have the same
magnetization sum. -/
theorem magEigenvalueS_eq_iff (σ σ' : Λ → Fin (N + 1)) :
    magEigenvalueS σ = magEigenvalueS σ' ↔
      magSumS σ = magSumS σ' := by
  unfold magEigenvalueS
  constructor
  · intro h
    have h' : (magSumS σ : ℂ) = (magSumS σ' : ℂ) := by
      have h2 :
          -(magSumS σ : ℂ) + ((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 =
          -(magSumS σ' : ℂ) + ((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 := by
        have := h
        linear_combination this
      have h3 : -(magSumS σ : ℂ) = -(magSumS σ' : ℂ) :=
        add_right_cancel h2
      have h4 : (magSumS σ : ℂ) = (magSumS σ' : ℂ) := neg_injective h3
      exact h4
    exact_mod_cast h'
  · intro h
    rw [h]

omit [DecidableEq Λ] in
/-- `magEigenvalueS (fun _ => 0) = (|Λ| · N : ℂ)/2`. -/
theorem magEigenvalueS_const_zero :
    magEigenvalueS (fun _ : Λ => (0 : Fin (N + 1))) =
      (Fintype.card Λ : ℂ) * (N : ℂ) / 2 := by
  unfold magEigenvalueS
  rw [magSumS_const_zero]
  push_cast
  ring

omit [DecidableEq Λ] in
/-- `magEigenvalueS` of a constant configuration. The maximum value
`(|Λ| · N : ℂ)/2` is attained at `s = 0`; the minimum value
`-(|Λ| · N : ℂ)/2` at `s = N` (the natural number index of the lowest
weight state). -/
theorem magEigenvalueS_const (s : Fin (N + 1)) :
    magEigenvalueS (fun _ : Λ => s) =
      (Fintype.card Λ : ℂ) * ((N : ℂ) / 2 - (s.val : ℂ)) := by
  unfold magEigenvalueS
  rw [magSumS_const]
  push_cast
  ring


end LatticeSystem.Quantum
