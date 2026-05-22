import LatticeSystem.Quantum.SpinS.Theorem23Local

/-!
# Tasaki §2.5 Theorem 2.3 local lowering component API

This module contains the single-site lowering component formula,
Marshall-signed local lowering identities, and off-`A`/on-`A` filtered
sign-sum bounds used by the coefficient and local-difference layers of
Tasaki §2.5 Theorem 2.3. It is split from `Theorem23Local.lean` so the
core local ladder and site-sum expansion layer can elaborate separately
from the lowering component suffix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Single-site lowering components -/

/-- **Tasaki §2.5 Theorem 2.3 single-site lowering predecessor**:
if a target configuration `τ` in sector `M + 1` has positive local
value at `x`, lowering that local value by one gives a configuration
in sector `M`.

This is the magnetization bookkeeping behind the local component
formula for a single summand in `Ŝ^-_tot`. -/
private theorem magSumS_single_site_lowering_predecessor {M : ℕ}
    (τ : magConfigS V N (M + 1)) (x : V) (hx : 0 < (τ.1 x).val) :
    magSumS
        (Function.update τ.1 x
          ⟨(τ.1 x).val - 1, by omega⟩) = M := by
  classical
  have hsum_succ :
      magSumS
          (Function.update τ.1 x
            ⟨(τ.1 x).val - 1, by omega⟩) + 1 = magSumS τ.1 := by
    unfold magSumS
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    simp only [Function.update_self]
    have hrest :
        (∑ y ∈ (Finset.univ : Finset V) \ {x},
            (Function.update τ.1 x
              ⟨(τ.1 x).val - 1, by omega⟩ y).val) =
          ∑ y ∈ (Finset.univ : Finset V) \ {x}, (τ.1 y).val := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyx : y ≠ x := by
        simpa using hy
      rw [Function.update_of_ne hyx]
    rw [hrest]
    have hpred_val :
        (⟨(τ.1 x).val - 1, by
          omega⟩ : Fin (N + 1)).val + 1 = (τ.1 x).val := by
      simp
      omega
    omega
  have hτ : magSumS τ.1 = M + 1 := τ.2
  omega

/-- **Tasaki §2.5 Theorem 2.3 zero local lowering component**:
if the target configuration already has local value `0` at `x`, the
single-site lowering summand at `x` contributes zero to that target
component.

This is the boundary case for the local predecessor analysis of the
`Ŝ^-_tot` site-sum expansion. -/
theorem onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
    {M : ℕ} (Φ : magConfigS V N M → ℂ) (τ : magConfigS V N (M + 1))
    (x : V) (hx : (τ.1 x).val = 0) :
    (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1) = 0 := by
  classical
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro σ _hσ
  by_cases hoff : ∀ k, k ≠ x → τ.1 k = σ k
  · rw [onSiteS_apply_of_off_site_agree x _ hoff]
    have hnot_lower : (σ x).val + 1 ≠ (τ.1 x).val := by omega
    rw [spinSOpMinus_apply_other N hnot_lower, zero_mul]
  · rw [onSiteS_apply_eq_zero_of_off_site_diff x _ hoff, zero_mul]

/-- **Tasaki §2.5 Theorem 2.3 single-site lowering component**:
if a target sector configuration `τ` has positive local value at `x`,
then the `x`-summand of `Ŝ^-_tot` at `τ` is exactly the lowering matrix
coefficient times the source-sector coefficient at the unique
predecessor configuration obtained by decreasing `τ x` by one.

This is the local component formula needed before applying the
single-site Marshall predecessor sign lemmas in the adjacent-sector
positivity argument. -/
theorem onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred
    {M : ℕ} (Φ : magConfigS V N M → ℂ) (τ : magConfigS V N (M + 1))
    (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1) =
        spinSOpMinus N (τ.1 x) predVal *
          Φ ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩ := by
  classical
  dsimp only
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single
    (Function.update τ.1 x
      ⟨(τ.1 x).val - 1, by omega⟩)]
  · rw [onSiteS_apply_of_off_site_agree]
    · rw [magSectorEmbedding_apply_of_mem Φ
        (magSumS_single_site_lowering_predecessor τ x hx)]
      simp
    · intro y hy
      rw [Function.update_of_ne hy]
  · intro σ _hσ hσ_ne
    by_cases hoff : ∀ k, k ≠ x → τ.1 k = σ k
    · rw [onSiteS_apply_of_off_site_agree x _ hoff]
      have hnot_lower : (σ x).val + 1 ≠ (τ.1 x).val := by
        intro h_lower
        apply hσ_ne
        funext y
        by_cases hy : y = x
        · subst y
          apply Fin.ext
          simp
          omega
        · rw [Function.update_of_ne hy]
          exact (hoff y hy).symm
      rw [spinSOpMinus_apply_other N hnot_lower, zero_mul]
    · rw [onSiteS_apply_eq_zero_of_off_site_diff x _ hoff, zero_mul]
  · intro hnot_mem
    exact False.elim (hnot_mem (Finset.mem_univ _))

/-- **Tasaki §2.5 Theorem 2.3 single-site lowering real part**:
at a target configuration with positive local value, the real part of
the single-site lowering summand is the product of the positive
lowering matrix coefficient and the real part of the predecessor
coefficient.

This is the real-valued form of
`onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred`,
using that every `Ŝ^-` matrix entry is real. -/
theorem onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re
    {M : ℕ} (Φ : magConfigS V N M → ℂ) (τ : magConfigS V N (M + 1))
    (x : V) (hx : 0 < (τ.1 x).val) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1).re) =
        (spinSOpMinus N (τ.1 x) predVal).re *
          (Φ ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩).re := by
  classical
  dsimp only
  rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred
    Φ τ x hx]
  rw [Complex.mul_re, spinSOpMinus_apply_im_zero]
  ring

/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowered coefficient identity**:
if the lowered site lies outside `A`, then the signed real single-site
lowering contribution is the positive lowering coefficient times the
Marshall-signed predecessor coefficient.

This is the coefficient-level form behind
`tasaki23_signed_single_site_lowering_component_pos_of_A_false`; it is
the exact identity needed before summing the off-`A` contributions in
the lowered-vector Marshall-positivity argument. -/
theorem tasaki23_signed_single_site_lowering_component_eq_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hx : 0 < (τ.1 x).val) (hAx : A x = false) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    let hpredM : magSumS pred = M :=
      magSumS_single_site_lowering_predecessor τ x hx
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) =
      (spinSOpMinus N (τ.1 x) predVal).re *
        ((marshallSignS A pred).re * (Φ ⟨pred, hpredM⟩).re) := by
  classical
  dsimp only
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re := by
    simpa [predVal, pred, hpredM]
      using
        onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re
          Φ τ x hx
  have hoff : ∀ k, k ≠ x → τ.1 k = pred k := by
    intro k hk
    dsimp [pred]
    rw [Function.update_of_ne hk]
  have hsign_lower : (pred x).val + 1 = (τ.1 x).val := by
    dsimp [pred, predVal]
    simp
    omega
  have hsign :
      (marshallSignS A τ.1).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_false_lower
      A hAx hoff hsign_lower
  have hsq : (marshallSignS A pred).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_sq A pred
  have hsign_eq : (marshallSignS A τ.1).re = (marshallSignS A pred).re := by
    calc
      (marshallSignS A τ.1).re =
          (marshallSignS A τ.1).re * 1 := by ring
      _ =
          (marshallSignS A τ.1).re *
            ((marshallSignS A pred).re * (marshallSignS A pred).re) := by
          rw [hsq]
      _ =
          ((marshallSignS A τ.1).re * (marshallSignS A pred).re) *
            (marshallSignS A pred).re := by ring
      _ = 1 * (marshallSignS A pred).re := by rw [hsign]
      _ = (marshallSignS A pred).re := by ring
  rw [hcomponent]
  rw [hsign_eq]
  ring

/-- **Tasaki §2.5 Theorem 2.3 on-`A` lowered coefficient identity**:
if the lowered site lies inside `A`, then the signed real single-site
lowering contribution is the negative of the positive lowering
coefficient times the Marshall-signed predecessor coefficient.

This is the exact sign-reversal identity behind
`tasaki23_signed_single_site_lowering_component_neg_of_A_true`, and it
isolates the coefficient relation that the later dominance proof must
control after summing over sites in `A`. -/
theorem tasaki23_signed_single_site_lowering_component_eq_neg_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hx : 0 < (τ.1 x).val) (hAx : A x = true) :
    let predVal : Fin (N + 1) :=
      ⟨(τ.1 x).val - 1, by omega⟩
    let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
    let hpredM : magSumS pred = M :=
      magSumS_single_site_lowering_predecessor τ x hx
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) =
      -((spinSOpMinus N (τ.1 x) predVal).re *
        ((marshallSignS A pred).re * (Φ ⟨pred, hpredM⟩).re)) := by
  classical
  dsimp only
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re := by
    simpa [predVal, pred, hpredM]
      using
        onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re
          Φ τ x hx
  have hoff : ∀ k, k ≠ x → τ.1 k = pred k := by
    intro k hk
    dsimp [pred]
    rw [Function.update_of_ne hk]
  have hsign_lower : (pred x).val + 1 = (τ.1 x).val := by
    dsimp [pred, predVal]
    simp
    omega
  have hsign :
      (marshallSignS A τ.1).re * (marshallSignS A pred).re = -1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_true_lower
      A hAx hoff hsign_lower
  have hsq : (marshallSignS A pred).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_sq A pred
  have hsign_eq : (marshallSignS A τ.1).re = - (marshallSignS A pred).re := by
    calc
      (marshallSignS A τ.1).re =
          (marshallSignS A τ.1).re * 1 := by ring
      _ =
          (marshallSignS A τ.1).re *
            ((marshallSignS A pred).re * (marshallSignS A pred).re) := by
          rw [hsq]
      _ =
          ((marshallSignS A τ.1).re * (marshallSignS A pred).re) *
            (marshallSignS A pred).re := by ring
      _ = (-1) * (marshallSignS A pred).re := by rw [hsign]
      _ = - (marshallSignS A pred).re := by ring
  rw [hcomponent]
  rw [hsign_eq]
  ring

/-- **Tasaki §2.5 Theorem 2.3 off-`A` single-site positivity**:
if the lowered site lies outside `A`, then the signed real part of its
single-site lowering contribution is strictly positive whenever the
source-sector vector is Marshall-positive.

This combines the predecessor component formula with the off-`A`
Marshall sign preservation under a one-step lowering. -/
theorem tasaki23_signed_single_site_lowering_component_pos_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hx : 0 < (τ.1 x).val) (hAx : A x = false)
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 < (marshallSignS A τ.1).re *
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) := by
  classical
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re := by
    simpa [predVal, pred, hpredM]
      using
        onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re
          Φ τ x hx
  have hcoef_lower : predVal.val + 1 = (τ.1 x).val := by
    dsimp [predVal]
    omega
  have hcoef_pos : 0 < (spinSOpMinus N (τ.1 x) predVal).re :=
    spinSOpMinus_apply_re_pos_of_lower N hcoef_lower
  have hoff : ∀ k, k ≠ x → τ.1 k = pred k := by
    intro k hk
    dsimp [pred]
    rw [Function.update_of_ne hk]
  have hsign_lower : (pred x).val + 1 = (τ.1 x).val := by
    dsimp [pred, predVal]
    simp
    omega
  have hsign :
      (marshallSignS A τ.1).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_false_lower
      A hAx hoff hsign_lower
  have hsq : (marshallSignS A pred).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_sq A pred
  have hsrc :
      0 < (marshallSignS A pred).re * (Φ ⟨pred, hpredM⟩).re :=
    hΦ_pos ⟨pred, hpredM⟩
  have htarget_src :
      0 < (marshallSignS A τ.1).re * (Φ ⟨pred, hpredM⟩).re := by
    nlinarith [hsign, hsq, hsrc]
  rw [hcomponent]
  have hrearrange :
      (marshallSignS A τ.1).re *
          ((spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re) =
        (spinSOpMinus N (τ.1 x) predVal).re *
          ((marshallSignS A τ.1).re * (Φ ⟨pred, hpredM⟩).re) := by
    ring
  rw [hrearrange]
  exact mul_pos hcoef_pos htarget_src

/-- **Tasaki §2.5 Theorem 2.3 on-`A` single-site negativity**:
if the lowered site lies in `A`, then the signed real part of its
single-site lowering contribution is strictly negative whenever the
source-sector vector is Marshall-positive.

The sign reversal is the complementary local case to
`tasaki23_signed_single_site_lowering_component_pos_of_A_false`. -/
theorem tasaki23_signed_single_site_lowering_component_neg_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hx : 0 < (τ.1 x).val) (hAx : A x = true)
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) < 0 := by
  classical
  let predVal : Fin (N + 1) := ⟨(τ.1 x).val - 1, by omega⟩
  let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
  have hpredM : magSumS pred = M :=
    magSumS_single_site_lowering_predecessor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re := by
    simpa [predVal, pred, hpredM]
      using
        onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re
          Φ τ x hx
  have hcoef_lower : predVal.val + 1 = (τ.1 x).val := by
    dsimp [predVal]
    omega
  have hcoef_pos : 0 < (spinSOpMinus N (τ.1 x) predVal).re :=
    spinSOpMinus_apply_re_pos_of_lower N hcoef_lower
  have hoff : ∀ k, k ≠ x → τ.1 k = pred k := by
    intro k hk
    dsimp [pred]
    rw [Function.update_of_ne hk]
  have hsign_lower : (pred x).val + 1 = (τ.1 x).val := by
    dsimp [pred, predVal]
    simp
    omega
  have hsign :
      (marshallSignS A τ.1).re * (marshallSignS A pred).re = -1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_true_lower
      A hAx hoff hsign_lower
  have hsq : (marshallSignS A pred).re * (marshallSignS A pred).re = 1 :=
    marshallSignS_re_sq A pred
  have hsrc :
      0 < (marshallSignS A pred).re * (Φ ⟨pred, hpredM⟩).re :=
    hΦ_pos ⟨pred, hpredM⟩
  have htarget_src :
      (marshallSignS A τ.1).re * (Φ ⟨pred, hpredM⟩).re < 0 := by
    nlinarith [hsign, hsq, hsrc]
  rw [hcomponent]
  have hrearrange :
      (marshallSignS A τ.1).re *
          ((spinSOpMinus N (τ.1 x) predVal).re *
            (Φ ⟨pred, hpredM⟩).re) =
        (spinSOpMinus N (τ.1 x) predVal).re *
          ((marshallSignS A τ.1).re * (Φ ⟨pred, hpredM⟩).re) := by
    ring
  rw [hrearrange]
  exact mul_neg_of_pos_of_neg hcoef_pos htarget_src

/-- **Tasaki §2.5 Theorem 2.3 off-`A` local lowering non-negativity**:
including the boundary case where the target local value is zero, the
signed single-site lowering contribution is non-negative at every site
outside `A`.

This is the weak boundary-inclusive form of
`tasaki23_signed_single_site_lowering_component_pos_of_A_false`. -/
theorem tasaki23_signed_single_site_lowering_component_nonneg_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hAx : A x = false)
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 ≤ (marshallSignS A τ.1).re *
      ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) := by
  by_cases hx : 0 < (τ.1 x).val
  · exact le_of_lt
      (tasaki23_signed_single_site_lowering_component_pos_of_A_false
        A Φ τ x hx hAx hΦ_pos)
  · have hzero : (τ.1 x).val = 0 := by omega
    rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
      Φ τ x hzero]
    simp

/-- **Tasaki §2.5 Theorem 2.3 on-`A` local lowering non-positivity**:
including the boundary case where the target local value is zero, the
signed single-site lowering contribution is non-positive at every site
inside `A`.

This is the weak boundary-inclusive form of
`tasaki23_signed_single_site_lowering_component_neg_of_A_true`. -/
theorem tasaki23_signed_single_site_lowering_component_nonpos_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hAx : A x = true)
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) ≤ 0 := by
  by_cases hx : 0 < (τ.1 x).val
  · exact le_of_lt
      (tasaki23_signed_single_site_lowering_component_neg_of_A_true
        A Φ τ x hx hAx hΦ_pos)
  · have hzero : (τ.1 x).val = 0 := by omega
    rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
      Φ τ x hzero]
    simp

/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowered sign-sum bound**:
the filtered sum of signed single-site lowering contributions over
sites outside `A` is non-negative.

This is the finite-sum form of
`tasaki23_signed_single_site_lowering_component_nonneg_of_A_false`. -/
theorem tasaki23_signed_lowering_offA_sum_nonneg
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 ≤ ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  apply Finset.sum_nonneg
  intro x hx
  have hAx : A x = false := by
    simpa using (Finset.mem_filter.mp hx).2
  exact tasaki23_signed_single_site_lowering_component_nonneg_of_A_false
    A Φ τ x hAx hΦ_pos

/-- **Tasaki §2.5 Theorem 2.3 on-`A` lowered sign-sum bound**:
the filtered sum of signed single-site lowering contributions over
sites inside `A` is non-positive.

This is the finite-sum form of
`tasaki23_signed_single_site_lowering_component_nonpos_of_A_true`. -/
theorem tasaki23_signed_lowering_onA_sum_nonpos
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro x hx
  have hAx : A x = true := by
    simpa using (Finset.mem_filter.mp hx).2
  exact tasaki23_signed_single_site_lowering_component_nonpos_of_A_true
    A Φ τ x hAx hΦ_pos


end LatticeSystem.Quantum
