import LatticeSystem.Quantum.SpinS.Theorem23LocalLowering

/-!
# Tasaki §2.5 Theorem 2.3 single-site lowering positivity

This module contains the single-site lowering positivity/negativity theorems,
split as a stable suffix from `Theorem23LocalLowering.lean`: for a
Marshall-positive real source vector, the signed single-site lowering component
is strictly positive at an off-`A` site and strictly negative at an on-`A`
site. The parent module keeps the raw single-site lowering component formulas
and the signed coefficient identities those positivity facts build on.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

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

end LatticeSystem.Quantum
