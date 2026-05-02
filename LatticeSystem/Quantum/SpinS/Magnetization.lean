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
/-- Definitional unfolding of `magSumS`. -/
theorem magSumS_def (σ : Λ → Fin (N + 1)) :
    magSumS σ = ∑ x : Λ, (σ x).val := rfl

omit [DecidableEq Λ] in
/-- `magSumS σ ≥ 0` always. -/
theorem magSumS_nonneg (σ : Λ → Fin (N + 1)) : 0 ≤ magSumS σ := by
  unfold magSumS
  exact Finset.sum_nonneg (fun _ _ => Nat.zero_le _)

omit [DecidableEq Λ] in
/-- The cast `(magSumS σ : ℝ) ≥ 0`. -/
theorem magSumS_real_nonneg (σ : Λ → Fin (N + 1)) :
    (0 : ℝ) ≤ (magSumS σ : ℝ) := by
  exact_mod_cast magSumS_nonneg σ

omit [DecidableEq Λ] in
/-- The cast `(magSumS σ : ℂ).re = (magSumS σ : ℝ)`. -/
theorem magSumS_complex_re (σ : Λ → Fin (N + 1)) :
    ((magSumS σ : ℂ)).re = (magSumS σ : ℝ) := by
  simp

omit [DecidableEq Λ] in
/-- The cast `(magSumS σ : ℂ).im = 0`. -/
theorem magSumS_complex_im (σ : Λ → Fin (N + 1)) :
    ((magSumS σ : ℂ)).im = 0 := by
  simp

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

/-- The zero vector lies in every magnetization subspace. -/
theorem zero_mem_magSubspaceS (M : ℂ) :
    (0 : (Λ → Fin (N + 1)) → ℂ) ∈ magSubspaceS Λ N M :=
  (magSubspaceS Λ N M).zero_mem

/-- Sum-membership for the magnetization subspace. -/
theorem add_mem_magSubspaceS (M : ℂ) {v w : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS Λ N M) (hw : w ∈ magSubspaceS Λ N M) :
    v + w ∈ magSubspaceS Λ N M :=
  (magSubspaceS Λ N M).add_mem hv hw

/-- Scalar multiplication membership. -/
theorem smul_mem_magSubspaceS (M : ℂ) (c : ℂ)
    {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ magSubspaceS Λ N M) :
    c • v ∈ magSubspaceS Λ N M :=
  (magSubspaceS Λ N M).smul_mem c hv

/-- Negation membership in `magSubspaceS`. -/
theorem neg_mem_magSubspaceS (M : ℂ)
    {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ magSubspaceS Λ N M) :
    -v ∈ magSubspaceS Λ N M :=
  (magSubspaceS Λ N M).neg_mem hv

/-- Subtraction membership in `magSubspaceS`. -/
theorem sub_mem_magSubspaceS (M : ℂ)
    {v w : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ magSubspaceS Λ N M)
    (hw : w ∈ magSubspaceS Λ N M) :
    v - w ∈ magSubspaceS Λ N M :=
  (magSubspaceS Λ N M).sub_mem hv hw

/-- `Finset.sum` membership in `magSubspaceS`. -/
theorem finset_sum_mem_magSubspaceS {ι : Type*} (M : ℂ)
    (s : Finset ι) (f : ι → (Λ → Fin (N + 1)) → ℂ)
    (hf : ∀ i ∈ s, f i ∈ magSubspaceS Λ N M) :
    (∑ i ∈ s, f i) ∈ magSubspaceS Λ N M :=
  (magSubspaceS Λ N M).sum_mem hf

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
/-- `magSumS (fun _ => Fin.last N) = |Λ| · N`. -/
theorem magSumS_const_last :
    magSumS (fun _ : Λ => (Fin.last N : Fin (N + 1))) =
      Fintype.card Λ * N := by
  rw [magSumS_const]
  rfl

omit [DecidableEq Λ] in
/-- `magSumS σ = magSumS σ`: trivial reflexivity. -/
theorem magSumS_refl (σ : Λ → Fin (N + 1)) :
    magSumS σ = magSumS σ := rfl

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
/-- The real part of `magEigenvalueS σ` is `(|Λ| · N : ℝ)/2 - magSumS σ`. -/
theorem magEigenvalueS_re (σ : Λ → Fin (N + 1)) :
    (magEigenvalueS σ).re =
      ((Fintype.card Λ : ℝ) * (N : ℝ)) / 2 - (magSumS σ : ℝ) := by
  unfold magEigenvalueS
  simp

omit [DecidableEq Λ] in
/-- `magEigenvalueS σ` is bounded: `(magEigenvalueS σ).re ≥ -(|Λ| · N) / 2`.
The most-down configuration `σ ≡ N` (giving `magSumS σ = |Λ| · N`)
gives the lowest value `-(|Λ| · N) / 2`. -/
theorem magEigenvalueS_re_lower_bound (σ : Λ → Fin (N + 1)) :
    -((Fintype.card Λ : ℝ) * (N : ℝ)) / 2 ≤ (magEigenvalueS σ).re := by
  rw [magEigenvalueS_re]
  have hle := magSumS_le σ
  have : (magSumS σ : ℝ) ≤ ((Fintype.card Λ : ℝ) * (N : ℝ)) := by
    have : ((magSumS σ : ℕ) : ℝ) ≤ ((Fintype.card Λ * N : ℕ) : ℝ) :=
      Nat.cast_le.mpr hle
    simp at this; linarith
  linarith

omit [DecidableEq Λ] in
/-- `magEigenvalueS σ` is bounded above: `(magEigenvalueS σ).re ≤ (|Λ| · N) / 2`.
The most-up configuration `σ ≡ 0` (giving `magSumS σ = 0`) gives the
highest value `(|Λ| · N) / 2`. -/
theorem magEigenvalueS_re_upper_bound (σ : Λ → Fin (N + 1)) :
    (magEigenvalueS σ).re ≤ ((Fintype.card Λ : ℝ) * (N : ℝ)) / 2 := by
  rw [magEigenvalueS_re]
  have hnn := magSumS_real_nonneg σ
  linarith

omit [DecidableEq Λ] in
/-- The absolute value of the magnetization eigenvalue is bounded by
`(|Λ| · N) / 2`. -/
theorem magEigenvalueS_re_abs_bound (σ : Λ → Fin (N + 1)) :
    |(magEigenvalueS σ).re| ≤ ((Fintype.card Λ : ℝ) * (N : ℝ)) / 2 := by
  rw [abs_le]
  refine ⟨?_, magEigenvalueS_re_upper_bound σ⟩
  have := magEigenvalueS_re_lower_bound (Λ := Λ) σ
  linarith


omit [DecidableEq Λ] in
/-- `magEigenvalueS σ = ((magEigenvalueS σ).re : ℂ)`: its imaginary
part vanishes, so it equals its embedded real part. -/
theorem magEigenvalueS_eq_ofReal_re (σ : Λ → Fin (N + 1)) :
    magEigenvalueS σ = ((magEigenvalueS σ).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [magEigenvalueS_im_zero]

/-- `Ŝ_tot^{(3)} · |σ⟩ = ((magEigenvalueS σ).re : ℂ) • |σ⟩` — the
real-eigenvalue form of `totalSpinSOp3_mulVec_basisVecS`. -/
theorem totalSpinSOp3_mulVec_basisVecS_real (σ : Λ → Fin (N + 1)) :
    (totalSpinSOp3 Λ N).mulVec (basisVecS σ) =
      ((magEigenvalueS σ).re : ℂ) • basisVecS σ := by
  rw [totalSpinSOp3_mulVec_basisVecS, ← magEigenvalueS_eq_ofReal_re]

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
/-- `magSumS σ ≥ (σ y).val` at any site `y`. -/
theorem magSumS_ge_of_exists (σ : Λ → Fin (N + 1)) (y : Λ) :
    (σ y).val ≤ magSumS σ := by
  unfold magSumS
  exact Finset.single_le_sum
    (f := fun x => (σ x).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)

omit [DecidableEq Λ] in
/-- `magSumS σ > 0` ↔ there exists `x` with `σ x ≠ 0`. -/
theorem magSumS_pos_iff (σ : Λ → Fin (N + 1)) :
    0 < magSumS σ ↔ ∃ x : Λ, σ x ≠ 0 := by
  rw [Nat.pos_iff_ne_zero]
  rw [Ne, magSumS_eq_zero_iff]
  push_neg
  rfl

omit [DecidableEq Λ] in
/-- For `N = 0` (`S = 0`), `magSumS σ = 0` always (the only Fin 1
value is 0). -/
theorem magSumS_of_N_zero (σ : Λ → Fin 1) :
    magSumS σ = 0 := by
  apply (magSumS_eq_zero_iff (N := 0) σ).mpr
  intro x
  apply Fin.ext
  have := (σ x).isLt
  omega

omit [DecidableEq Λ] in
/-- For `N = 0` (`S = 0`), `magEigenvalueS σ = 0` always. -/
theorem magEigenvalueS_of_N_zero (σ : Λ → Fin 1) :
    magEigenvalueS σ = 0 := by
  unfold magEigenvalueS
  rw [magSumS_of_N_zero σ]
  push_cast
  ring

omit [DecidableEq Λ] in
/-- `magSumS σ` over an empty lattice is `0`. -/
theorem magSumS_of_isEmpty [IsEmpty Λ] (σ : Λ → Fin (N + 1)) :
    magSumS σ = 0 := by
  unfold magSumS
  rw [Finset.sum_empty.symm]
  congr 1
  exact Finset.eq_empty_of_isEmpty _

omit [DecidableEq Λ] in
/-- `magEigenvalueS σ = 0` over an empty lattice. -/
theorem magEigenvalueS_of_isEmpty [IsEmpty Λ] (σ : Λ → Fin (N + 1)) :
    magEigenvalueS σ = 0 := by
  unfold magEigenvalueS
  rw [magSumS_of_isEmpty σ]
  have : (Fintype.card Λ : ℂ) = 0 := by
    have : Fintype.card Λ = 0 := Fintype.card_eq_zero
    exact_mod_cast this
  rw [this]
  ring

omit [DecidableEq Λ] in
/-- For `N = 0` (`S = 0`), `(magEigenvalueS σ).re = 0`. -/
theorem magEigenvalueS_re_of_N_zero (σ : Λ → Fin 1) :
    (magEigenvalueS (N := 0) σ).re = 0 := by
  rw [magEigenvalueS_of_N_zero σ]
  simp

omit [DecidableEq Λ] in
/-- For an empty lattice, `(magEigenvalueS σ).re = 0`. -/
theorem magEigenvalueS_re_of_isEmpty [IsEmpty Λ] (σ : Λ → Fin (N + 1)) :
    (magEigenvalueS σ).re = 0 := by
  rw [magEigenvalueS_of_isEmpty σ]
  simp

/-- For trivial spin (`N = 0`), `magSubspaceS Λ 0 0 = ⊤`: every
vector is in the zero-magnetization subspace because every basis
state has eigenvalue 0. -/
theorem magSubspaceS_N_zero_zero_eq_top :
    magSubspaceS Λ 0 0 = ⊤ := by
  refine eq_top_iff.mpr (fun v _ => ?_)
  rw [mem_magSubspaceS_iff]
  rw [show (totalSpinSOp3 Λ 0 : ManyBodyOpS Λ 0) = 0 from
    totalSpinSOp3_N_zero (Λ := Λ)]
  rw [Matrix.zero_mulVec]
  simp

/-- For trivial spin (`N = 0`) and `M ≠ 0`, `magSubspaceS Λ 0 M = ⊥`:
no vector has nonzero magnetization since `Ŝ_tot^{(3)} = 0`. -/
theorem magSubspaceS_N_zero_ne_zero_eq_bot {M : ℂ} (hM : M ≠ 0) :
    magSubspaceS Λ 0 M = ⊥ := by
  refine eq_bot_iff.mpr (fun v hv => ?_)
  rw [mem_magSubspaceS_iff] at hv
  rw [show (totalSpinSOp3 Λ 0 : ManyBodyOpS Λ 0) = 0 from
    totalSpinSOp3_N_zero (Λ := Λ)] at hv
  rw [Matrix.zero_mulVec] at hv
  -- hv : 0 = M • v
  rw [Submodule.mem_bot]
  have : M • v = 0 := hv.symm
  rcases smul_eq_zero.mp this with hM' | hv'
  · exact (hM hM').elim
  · exact hv'

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

omit [DecidableEq Λ] in
/-- `magEigenvalueS_re` at the all-zero config: `(|Λ| · N : ℝ)/2`. -/
theorem magEigenvalueS_re_const_zero :
    (magEigenvalueS (fun _ : Λ => (0 : Fin (N + 1)))).re =
      (Fintype.card Λ : ℝ) * (N : ℝ) / 2 := by
  rw [magEigenvalueS_const_zero]
  simp

omit [DecidableEq Λ] in
/-- `magEigenvalueS_re` at the all-`Fin.last N` config: `-((|Λ| · N : ℝ)/2)`. -/
theorem magEigenvalueS_re_const_last :
    (magEigenvalueS (fun _ : Λ => (Fin.last N : Fin (N + 1)))).re =
      -((Fintype.card Λ : ℝ) * (N : ℝ) / 2) := by
  rw [magEigenvalueS_const_last]
  simp

end LatticeSystem.Quantum
