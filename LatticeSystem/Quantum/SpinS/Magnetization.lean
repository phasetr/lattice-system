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
/-- `magSumS σ ≥ 0` always. -/
theorem magSumS_nonneg (σ : Λ → Fin (N + 1)) : 0 ≤ magSumS σ := by
  unfold magSumS
  exact Finset.sum_nonneg (fun _ _ => Nat.zero_le _)

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

omit [DecidableEq Λ] in
/-- `magSumS σ = |Λ| · N` iff `σ x = Fin.last N` for every `x : Λ`
(the lowest-weight all-`Fin.last N` config achieves the maximum). -/
theorem magSumS_eq_max_iff (σ : Λ → Fin (N + 1)) :
    magSumS σ = Fintype.card Λ * N ↔ ∀ x : Λ, σ x = Fin.last N := by
  unfold magSumS
  constructor
  · intro h x
    -- If `magSumS σ = |Λ| · N`, then each `(σ x).val = N` (max).
    have hle : ∀ y ∈ (Finset.univ : Finset Λ), (σ y).val ≤ N :=
      fun y _ => by have := (σ y).isLt; omega
    have hsum_eq : ∀ y ∈ (Finset.univ : Finset Λ), (σ y).val = N := by
      apply (Finset.sum_eq_sum_iff_of_le hle).mp
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      exact h
    apply Fin.ext
    rw [hsum_eq x (Finset.mem_univ x)]
    rfl
  · intro h
    have heq : ∀ x : Λ, (σ x).val = N := fun x => by rw [h x]; rfl
    rw [Finset.sum_congr rfl (fun x _ => heq x)]
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

/-! ## Constant configurations -/

omit [DecidableEq Λ] in
/-- `magSumS` of a constant configuration `(fun _ => s)` is `|Λ| · s.val`. -/
theorem magSumS_const (s : Fin (N + 1)) :
    magSumS (fun _ : Λ => s) = Fintype.card Λ * s.val := by
  unfold magSumS
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [DecidableEq Λ] in
/-- `magSumS (fun _ => 0) = 0`. -/
theorem magSumS_const_zero :
    magSumS (fun _ : Λ => (0 : Fin (N + 1))) = 0 := by
  rw [magSumS_const]
  simp

omit [DecidableEq Λ] in
/-- `magSumS σ = 0` iff `σ x = 0` for every `x : Λ`. -/
theorem magSumS_eq_zero_iff (σ : Λ → Fin (N + 1)) :
    magSumS σ = 0 ↔ ∀ x : Λ, σ x = 0 := by
  unfold magSumS
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h x
    have := h x (Finset.mem_univ x)
    apply Fin.ext
    exact this
  · intro h x _
    rw [h x]
    rfl

omit [DecidableEq Λ] in
/-- `magEigenvalueS σ = 0` ↔ `magSumS σ = |Λ| · N / 2` (the
half-occupation condition). For spin-1/2 (`N = 1`) this means the
configuration has equal numbers of up/down spins. -/
theorem magEigenvalueS_eq_zero_iff (σ : Λ → Fin (N + 1)) :
    magEigenvalueS σ = 0 ↔
      ((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 = (magSumS σ : ℂ) := by
  unfold magEigenvalueS
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    rw [← h]
    ring

omit [DecidableEq Λ] in
/-- `magEigenvalueS σ ∈ ℝ`: the eigenvalue is real-valued (its
imaginary part is zero). The eigenvalue is constructed as
`(|Λ| · N : ℂ)/2 - magSumS σ`, both terms real. -/
theorem magEigenvalueS_im_zero (σ : Λ → Fin (N + 1)) :
    (magEigenvalueS σ).im = 0 := by
  unfold magEigenvalueS
  simp

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

omit [DecidableEq Λ] in
/-- `magEigenvalueS` at the lowest-weight all-`Fin.last N` config:
`-((|Λ| · N : ℂ)/2)`, the minimum eigenvalue of `Ŝ_tot^{(3)}`. -/
theorem magEigenvalueS_const_last :
    magEigenvalueS (fun _ : Λ => (Fin.last N : Fin (N + 1))) =
      -((Fintype.card Λ : ℂ) * (N : ℂ) / 2) := by
  rw [magEigenvalueS_const]
  simp [Fin.val_last]
  ring

end LatticeSystem.Quantum
