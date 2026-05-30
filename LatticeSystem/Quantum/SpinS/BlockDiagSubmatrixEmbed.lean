import LatticeSystem.Quantum.SpinS.BlockDiagSubmatrixBridge

set_option linter.unusedSectionVars false

/-!
# Reverse direction of block-diag bridge: submatrix eig embeds into full eig ⊓ ker(P)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

(h.1): for a parity-block-diagonal complex matrix `M`, the parity-`p` submatrix's
ν-eigenspace embeds injectively into `eig M ν ⊓ ker(P=(-1)^p)` via zero-extension off
`parityConfigS Λ N p`.  Combined with the forward direction (#3832), this gives the
**finrank equality**:
```
finrank ℂ (eig M.submatrix ν) = finrank ℂ (eig M ν ⊓ ker(P=(-1)^p))
```
for `p < 2`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Zero-extension off `parityConfigS Λ N p`** of a submatrix-indexed function. -/
private noncomputable def extendFromParity {p : ℕ}
    (w : parityConfigS Λ N p → ℂ) : (Λ → Fin (N + 1)) → ℂ :=
  fun σ => if hσ : magSumS σ % 2 = p then w ⟨σ, hσ⟩ else 0

/-- Value of the zero-extension at a parity-`p` configuration: the original `w` value. -/
private theorem extendFromParity_of_parity {p : ℕ}
    (w : parityConfigS Λ N p → ℂ) {σ : Λ → Fin (N + 1)} (hσ : magSumS σ % 2 = p) :
    extendFromParity w σ = w ⟨σ, hσ⟩ := by
  unfold extendFromParity; rw [dif_pos hσ]

/-- Value of the zero-extension off the parity-`p` slice: zero. -/
private theorem extendFromParity_of_other {p : ℕ}
    (w : parityConfigS Λ N p → ℂ) {σ : Λ → Fin (N + 1)} (hσ : magSumS σ % 2 ≠ p) :
    extendFromParity w σ = 0 := by
  unfold extendFromParity; rw [dif_neg hσ]

/-- Additivity of the zero-extension map. -/
private theorem extendFromParity_add {p : ℕ} (u v : parityConfigS Λ N p → ℂ) :
    extendFromParity (u + v) = extendFromParity u + extendFromParity v := by
  funext σ
  change extendFromParity (u + v) σ = extendFromParity u σ + extendFromParity v σ
  unfold extendFromParity
  split_ifs with hσ
  · rfl
  · simp

/-- Scalar compatibility of the zero-extension map. -/
private theorem extendFromParity_smul {p : ℕ} (c : ℂ) (v : parityConfigS Λ N p → ℂ) :
    extendFromParity (c • v) = c • extendFromParity v := by
  funext σ
  change extendFromParity (c • v) σ = c • extendFromParity v σ
  unfold extendFromParity
  split_ifs with hσ
  · rfl
  · simp

/-- **Matrix-vector product on a zero-extension** equals the submatrix matrix-vector product
on the parity-`p` configurations, plus zero contributions from cross-parity entries (using
block-diagonality of `M`). -/
private theorem mulVec_extendFromParity_at_parity
    {M : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ}
    {p : ℕ} (w : parityConfigS Λ N p → ℂ)
    {σ : Λ → Fin (N + 1)} (_hσ : magSumS σ % 2 = p) :
    (Matrix.mulVec M (extendFromParity w)) σ =
      ∑ τ : parityConfigS Λ N p, M σ τ.1 * w τ := by
  -- Full sum: ∑ τ : Λ → Fin (N+1), M σ τ * extendFromParity w τ.
  -- The terms with parity τ ≠ p contribute 0 (extension = 0).
  -- The terms with parity τ = p match the subtype sum.
  change ∑ τ : Λ → Fin (N + 1), M σ τ * extendFromParity w τ = _
  -- Convert subtype sum on the right to a sum over the filtered universe.
  rw [show (∑ τ : parityConfigS Λ N p, M σ τ.1 * w τ) =
        ∑ τ : { x : Λ → Fin (N + 1) // magSumS x % 2 = p },
          M σ τ.1 * extendFromParity w τ.1 from ?_]
  · -- Now apply Finset.sum_subtype to convert the subtype sum to a filter sum.
    rw [show (∑ τ : { x : Λ → Fin (N + 1) // magSumS x % 2 = p },
              M σ τ.1 * extendFromParity w τ.1) =
            ∑ τ ∈ (Finset.univ : Finset (Λ → Fin (N + 1))).filter
              (fun τ => magSumS τ % 2 = p), M σ τ * extendFromParity w τ from ?_]
    · -- Now full sum = filter sum + filter-not sum; the latter is 0.
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun τ : Λ → Fin (N + 1) => magSumS τ % 2 = p)
            (fun τ => M σ τ * extendFromParity w τ)]
      rw [show (∑ τ ∈ Finset.univ.filter (fun τ : Λ → Fin (N + 1) => ¬(magSumS τ % 2 = p)),
                M σ τ * extendFromParity w τ) = 0 from ?_]
      · rw [add_zero]
      · refine Finset.sum_eq_zero fun τ hτ => ?_
        have h_ext_zero : extendFromParity w τ = 0 :=
          extendFromParity_of_other w (Finset.mem_filter.mp hτ).2
        rw [h_ext_zero, mul_zero]
    · -- subtype sum = filter sum (Finset.sum_subtype.symm).
      exact (Finset.sum_subtype
        (Finset.univ.filter (fun τ : Λ → Fin (N + 1) => magSumS τ % 2 = p))
        (fun x => by simp)
        (fun τ => M σ τ * extendFromParity w τ)).symm
  · -- subtype sum form change: M σ τ.1 * w τ = M σ τ.1 * extendFromParity w τ.1
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h_ext_eq : extendFromParity w τ.1 = w ⟨τ.1, τ.2⟩ :=
      extendFromParity_of_parity w τ.2
    rw [h_ext_eq]
    congr 1

/-- **The zero-extension linear map** from submatrix eigenspace into full eigenspace ⊓ ker(P). -/
noncomputable def parityEmbedMap
    {M : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ}
    (hM_block : ∀ σ τ : Λ → Fin (N + 1), magSumS σ % 2 ≠ magSumS τ % 2 → M σ τ = 0)
    (p : ℕ) (ν : ℂ) :
    ↥(End.eigenspace (Matrix.toLin' (M.submatrix
      (fun σ : parityConfigS Λ N p => σ.1)
      (fun σ : parityConfigS Λ N p => σ.1))) ν) →ₗ[ℂ]
    ↥(End.eigenspace (Matrix.toLin' M) ν ⊓
      End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) ((-1 : ℂ) ^ p)) where
  toFun w := ⟨extendFromParity w.1, by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · -- M *ᵥ extend = ν • extend
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
      funext σ
      by_cases hσ : magSumS σ % 2 = p
      · -- σ has parity p
        have hsub_eig : (Matrix.toLin' (M.submatrix
            (fun σ : parityConfigS Λ N p => σ.1)
            (fun σ : parityConfigS Λ N p => σ.1))) w.1 = ν • w.1 :=
          End.mem_eigenspace_iff.mp w.2
        rw [Matrix.toLin'_apply] at hsub_eig
        have hsub_σ := congrFun hsub_eig ⟨σ, hσ⟩
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
          Matrix.submatrix_apply] at hsub_σ
        rw [mulVec_extendFromParity_at_parity w.1 hσ]
        rw [Pi.smul_apply, smul_eq_mul, extendFromParity_of_parity w.1 hσ]
        exact hsub_σ
      · -- σ has parity ≠ p
        rw [Pi.smul_apply, smul_eq_mul, extendFromParity_of_other w.1 hσ, mul_zero]
        -- Goal: (M *ᵥ extend w.1) σ = 0
        -- M σ τ * extend w.1 τ = 0 always:
        --   if τ has parity p, M σ τ = 0 (block-diag, σ has parity ≠ p).
        --   if τ has parity ≠ p, extend = 0.
        change ∑ τ : Λ → Fin (N + 1), M σ τ * extendFromParity w.1 τ = 0
        refine Finset.sum_eq_zero fun τ _ => ?_
        by_cases hτ : magSumS τ % 2 = p
        · have hne_par : magSumS σ % 2 ≠ magSumS τ % 2 := by
            have h_σ : magSumS σ % 2 < 2 := Nat.mod_lt _ (by norm_num)
            have h_τ : magSumS τ % 2 < 2 := Nat.mod_lt _ (by norm_num)
            omega
          rw [hM_block σ τ hne_par, zero_mul]
        · rw [extendFromParity_of_other w.1 hτ, mul_zero]
    · -- magParityDiagS *ᵥ extend = (-1)^p • extend
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
      funext σ
      simp only [magParityDiagS, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hσ : magSumS σ % 2 = p
      · -- σ has parity p; extension nonzero, value at σ = w ⟨σ, hσ⟩.
        congr 1
        rcases Nat.even_or_odd (magSumS σ) with he | ho
        · rw [Even.neg_one_pow he, Even.neg_one_pow (by rw [Nat.even_iff] at he ⊢; omega)]
        · rw [Odd.neg_one_pow ho, Odd.neg_one_pow (by rw [Nat.odd_iff] at ho ⊢; omega)]
      · -- σ doesn't have parity p; extension = 0; both sides = 0.
        rw [extendFromParity_of_other w.1 hσ, mul_zero, mul_zero]⟩
  map_add' u v := by
    apply Subtype.ext
    funext σ
    change extendFromParity (u.1 + v.1) σ = _
    rw [extendFromParity_add]
    rfl
  map_smul' c v := by
    apply Subtype.ext
    funext σ
    change extendFromParity (c • v.1) σ = _
    rw [extendFromParity_smul]
    rfl

/-- **`(h.1)` block-diag bridge reverse**: parity-`p` submatrix eigenspace embeds into
full eigenspace ⊓ `(-1)^p` ker of `magParityDiagS`. -/
theorem parity_block_submatrix_eigenspace_finrank_le_full_inter
    {M : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ}
    (hM_block : ∀ σ τ : Λ → Fin (N + 1), magSumS σ % 2 ≠ magSumS τ % 2 → M σ τ = 0)
    (p : ℕ) (ν : ℂ) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin' (M.submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1))) ν) ≤
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' M) ν ⊓
        End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) ((-1 : ℂ) ^ p)) := by
  have hinj : Function.Injective (parityEmbedMap hM_block p ν) := by
    intro u v huv
    apply Subtype.ext
    funext σ
    have huv_σ : extendFromParity u.1 σ.1 = extendFromParity v.1 σ.1 :=
      congrArg (fun w => w.1 σ.1) huv
    rw [extendFromParity_of_parity u.1 σ.2,
        extendFromParity_of_parity v.1 σ.2] at huv_σ
    exact huv_σ
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- **Finrank equality on block-diagonal matrices** combining forward (#3832) and reverse.
Requires `p < 2` (a hypothesis of the forward direction #3832). -/
theorem parity_block_submatrix_full_inter_finrank_eq
    {M : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ}
    (hM_block : ∀ σ τ : Λ → Fin (N + 1), magSumS σ % 2 ≠ magSumS τ % 2 → M σ τ = 0)
    {p : ℕ} (hp : p < 2) (ν : ℂ) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin' (M.submatrix
        (fun σ : parityConfigS Λ N p => σ.1)
        (fun σ : parityConfigS Λ N p => σ.1))) ν) =
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' M) ν ⊓
        End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) ((-1 : ℂ) ^ p)) :=
  le_antisymm
    (parity_block_submatrix_eigenspace_finrank_le_full_inter hM_block p ν)
    (parity_block_full_eigenspace_inter_finrank_le_submatrix hM_block hp ν)

end LatticeSystem.Quantum
