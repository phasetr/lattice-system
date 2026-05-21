import LatticeSystem.Quantum.SpinS.Theorem23LocalDifference

/-!
# Tasaki §2.5 Theorem 2.3 local-difference raising API

This module contains the raising-direction site-sum API split from
`Theorem23LocalDifference.lean`. The lowered predecessor-difference and
lowered site-sum API remains in `Theorem23LocalDifference.lean`, while
final Marshall-positivity wrappers are isolated in
`Theorem23LocalDifferenceMarshall.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 single-site raising successor**:
if a target configuration `τ` in sector `M` has local value below `N`
at `x`, raising that local value by one gives a configuration in
sector `M + 1`.

This private copy keeps the split raising-direction local component
API independent of the base module's private helper. -/
private theorem magSumS_single_site_raising_successor {M : ℕ}
    (τ : magConfigS V N M) (x : V) (hx : (τ.1 x).val < N) :
    magSumS
        (Function.update τ.1 x
          ⟨(τ.1 x).val + 1, by omega⟩) = M + 1 := by
  classical
  have hsum :
      magSumS
          (Function.update τ.1 x
            ⟨(τ.1 x).val + 1, by omega⟩) =
        magSumS τ.1 + 1 := by
    unfold magSumS
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ x)]
    simp only [Function.update_self]
    have hrest :
        (∑ y ∈ (Finset.univ : Finset V) \ {x},
            (Function.update τ.1 x
              ⟨(τ.1 x).val + 1, by omega⟩ y).val) =
          ∑ y ∈ (Finset.univ : Finset V) \ {x}, (τ.1 y).val := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyx : y ≠ x := by
        simpa using hy
      rw [Function.update_of_ne hyx]
    rw [hrest]
    omega
  have hτ : magSumS τ.1 = M := τ.2
  omega

/-- **Tasaki §2.5 Theorem 2.3 zero local raising component**:
if the target configuration already has local value `N` at `x`, the
single-site raising summand at `x` contributes zero to that target
component.

This is the boundary case for the raising-direction local successor
analysis of the `Ŝ^+_tot` site-sum expansion. -/
theorem onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_top
    {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ) (τ : magConfigS V N M)
    (x : V) (hx : (τ.1 x).val = N) :
    (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1) = 0 := by
  classical
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro σ _hσ
  by_cases hoff : ∀ k, k ≠ x → τ.1 k = σ k
  · rw [onSiteS_apply_of_off_site_agree x _ hoff]
    have hnot_raise : (τ.1 x).val + 1 ≠ (σ x).val := by
      have hσx : (σ x).val ≤ N := by have := (σ x).isLt; omega
      omega
    rw [spinSOpPlus_apply_other N hnot_raise, zero_mul]
  · rw [onSiteS_apply_eq_zero_of_off_site_diff x _ hoff, zero_mul]

/-- **Tasaki §2.5 Theorem 2.3 single-site raising component**:
if a target sector configuration `τ` has local value below `N` at
`x`, then the `x`-summand of `Ŝ^+_tot` at `τ` is exactly the raising
matrix coefficient times the source-sector coefficient at the unique
successor configuration obtained by increasing `τ x` by one.

This is the raising-direction companion to
`onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred`. -/
theorem onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_single_site_succ
    {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ) (τ : magConfigS V N M)
    (x : V) (hx : (τ.1 x).val < N) :
    let succVal : Fin (N + 1) :=
      ⟨(τ.1 x).val + 1, by omega⟩
    let succ : V → Fin (N + 1) := Function.update τ.1 x succVal
    (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1) =
        spinSOpPlus N (τ.1 x) succVal *
          Φ ⟨succ, magSumS_single_site_raising_successor τ x hx⟩ := by
  classical
  dsimp only
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single
    (Function.update τ.1 x
      ⟨(τ.1 x).val + 1, by omega⟩)]
  · rw [onSiteS_apply_of_off_site_agree]
    · rw [magSectorEmbedding_apply_of_mem Φ
        (magSumS_single_site_raising_successor τ x hx)]
      simp
    · intro y hy
      rw [Function.update_of_ne hy]
  · intro σ _hσ hσ_ne
    by_cases hoff : ∀ k, k ≠ x → τ.1 k = σ k
    · rw [onSiteS_apply_of_off_site_agree x _ hoff]
      have hnot_raise : (τ.1 x).val + 1 ≠ (σ x).val := by
        intro h_raise
        apply hσ_ne
        funext y
        by_cases hy : y = x
        · subst y
          apply Fin.ext
          simp
          omega
        · rw [Function.update_of_ne hy]
          exact (hoff y hy).symm
      rw [spinSOpPlus_apply_other N hnot_raise, zero_mul]
    · rw [onSiteS_apply_eq_zero_of_off_site_diff x _ hoff, zero_mul]
  · intro hnot_mem
    exact False.elim (hnot_mem (Finset.mem_univ _))

/-- **Tasaki §2.5 Theorem 2.3 single-site raising real part**:
at a target configuration whose local value is below `N`, the real
part of the single-site raising summand is the product of the positive
raising matrix coefficient and the real part of the successor
coefficient.

This is the real-valued raising-direction companion to
`onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_single_site_pred_re`. -/
theorem onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_single_site_succ_re
    {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ) (τ : magConfigS V N M)
    (x : V) (hx : (τ.1 x).val < N) :
    let succVal : Fin (N + 1) :=
      ⟨(τ.1 x).val + 1, by omega⟩
    let succ : V → Fin (N + 1) := Function.update τ.1 x succVal
    ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1).re) =
        (spinSOpPlus N (τ.1 x) succVal).re *
          (Φ ⟨succ, magSumS_single_site_raising_successor τ x hx⟩).re := by
  classical
  dsimp only
  rw [onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_single_site_succ
    Φ τ x hx]
  rw [Complex.mul_re, spinSOpPlus_apply_im_zero]
  ring

/-- **Tasaki §2.5 Theorem 2.3 off-`A` single-site raising positivity**:
if the raised site lies outside `A`, then the signed real part of its
single-site raising contribution is strictly positive whenever the
source-sector vector is Marshall-positive.

This is the raising-direction counterpart of
`tasaki23_signed_single_site_lowering_component_pos_of_A_false`. -/
theorem tasaki23_signed_single_site_raising_component_pos_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) (x : V)
    (hx : (τ.1 x).val < N) (hAx : A x = false)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 < (marshallSignS A τ.1).re *
      ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) := by
  classical
  let succVal : Fin (N + 1) := ⟨(τ.1 x).val + 1, by omega⟩
  let succ : V → Fin (N + 1) := Function.update τ.1 x succVal
  have hsuccM : magSumS succ = M + 1 :=
    magSumS_single_site_raising_successor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpPlus N (τ.1 x) succVal).re *
            (Φ ⟨succ, hsuccM⟩).re := by
    simpa [succVal, succ, hsuccM]
      using
        onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_single_site_succ_re
          Φ τ x hx
  have hcoef_raise : (τ.1 x).val + 1 = succVal.val := by
    dsimp [succVal]
  have hcoef_pos : 0 < (spinSOpPlus N (τ.1 x) succVal).re :=
    spinSOpPlus_apply_re_pos_of_raise N hcoef_raise
  have hoff : ∀ k, k ≠ x → succ k = τ.1 k := by
    intro k hk
    dsimp [succ]
    rw [Function.update_of_ne hk]
  have hsign_raise : (τ.1 x).val + 1 = (succ x).val := by
    dsimp [succ, succVal]
    simp
  have hsign :
      (marshallSignS A succ).re * (marshallSignS A τ.1).re = 1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_false_lower
      A hAx hoff hsign_raise
  have hsign_target :
      (marshallSignS A τ.1).re * (marshallSignS A succ).re = 1 := by
    rw [mul_comm]
    exact hsign
  have hsq : (marshallSignS A succ).re * (marshallSignS A succ).re = 1 :=
    marshallSignS_re_sq A succ
  have hsrc :
      0 < (marshallSignS A succ).re * (Φ ⟨succ, hsuccM⟩).re :=
    hΦ_pos ⟨succ, hsuccM⟩
  have htarget_src :
      0 < (marshallSignS A τ.1).re * (Φ ⟨succ, hsuccM⟩).re := by
    nlinarith [hsign_target, hsq, hsrc]
  rw [hcomponent]
  have hrearrange :
      (marshallSignS A τ.1).re *
          ((spinSOpPlus N (τ.1 x) succVal).re *
            (Φ ⟨succ, hsuccM⟩).re) =
        (spinSOpPlus N (τ.1 x) succVal).re *
          ((marshallSignS A τ.1).re * (Φ ⟨succ, hsuccM⟩).re) := by
    ring
  rw [hrearrange]
  exact mul_pos hcoef_pos htarget_src

/-- **Tasaki §2.5 Theorem 2.3 on-`A` single-site raising negativity**:
if the raised site lies in `A`, then the signed real part of its
single-site raising contribution is strictly negative whenever the
source-sector vector is Marshall-positive.

This is the raising-direction counterpart of
`tasaki23_signed_single_site_lowering_component_neg_of_A_true`. -/
theorem tasaki23_signed_single_site_raising_component_neg_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) (x : V)
    (hx : (τ.1 x).val < N) (hAx : A x = true)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) < 0 := by
  classical
  let succVal : Fin (N + 1) := ⟨(τ.1 x).val + 1, by omega⟩
  let succ : V → Fin (N + 1) := Function.update τ.1 x succVal
  have hsuccM : magSumS succ = M + 1 :=
    magSumS_single_site_raising_successor τ x hx
  have hcomponent :
      ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) =
          (spinSOpPlus N (τ.1 x) succVal).re *
            (Φ ⟨succ, hsuccM⟩).re := by
    simpa [succVal, succ, hsuccM]
      using
        onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_single_site_succ_re
          Φ τ x hx
  have hcoef_raise : (τ.1 x).val + 1 = succVal.val := by
    dsimp [succVal]
  have hcoef_pos : 0 < (spinSOpPlus N (τ.1 x) succVal).re :=
    spinSOpPlus_apply_re_pos_of_raise N hcoef_raise
  have hoff : ∀ k, k ≠ x → succ k = τ.1 k := by
    intro k hk
    dsimp [succ]
    rw [Function.update_of_ne hk]
  have hsign_raise : (τ.1 x).val + 1 = (succ x).val := by
    dsimp [succ, succVal]
    simp
  have hsign :
      (marshallSignS A succ).re * (marshallSignS A τ.1).re = -1 :=
    marshallSignS_re_mul_re_of_agree_off_site_A_true_lower
      A hAx hoff hsign_raise
  have hsign_target :
      (marshallSignS A τ.1).re * (marshallSignS A succ).re = -1 := by
    rw [mul_comm]
    exact hsign
  have hsq : (marshallSignS A succ).re * (marshallSignS A succ).re = 1 :=
    marshallSignS_re_sq A succ
  have hsrc :
      0 < (marshallSignS A succ).re * (Φ ⟨succ, hsuccM⟩).re :=
    hΦ_pos ⟨succ, hsuccM⟩
  have htarget_src :
      (marshallSignS A τ.1).re * (Φ ⟨succ, hsuccM⟩).re < 0 := by
    nlinarith [hsign_target, hsq, hsrc]
  rw [hcomponent]
  have hrearrange :
      (marshallSignS A τ.1).re *
          ((spinSOpPlus N (τ.1 x) succVal).re *
            (Φ ⟨succ, hsuccM⟩).re) =
        (spinSOpPlus N (τ.1 x) succVal).re *
          ((marshallSignS A τ.1).re * (Φ ⟨succ, hsuccM⟩).re) := by
    ring
  rw [hrearrange]
  exact mul_neg_of_pos_of_neg hcoef_pos htarget_src

/-- **Tasaki §2.5 Theorem 2.3 off-`A` local raising non-negativity**:
including the boundary case where the target local value is already
`N`, the signed single-site raising contribution is non-negative at
every site outside `A`.

This is the weak boundary-inclusive form of
`tasaki23_signed_single_site_raising_component_pos_of_A_false`. -/
theorem tasaki23_signed_single_site_raising_component_nonneg_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) (x : V)
    (hAx : A x = false)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 ≤ (marshallSignS A τ.1).re *
      ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
        (magSectorEmbedding Φ)) τ.1).re) := by
  by_cases hx : (τ.1 x).val < N
  · exact le_of_lt
      (tasaki23_signed_single_site_raising_component_pos_of_A_false
        A Φ τ x hx hAx hΦ_pos)
  · have htop : (τ.1 x).val = N := by
      have hle : (τ.1 x).val ≤ N := by
        have := (τ.1 x).isLt
        omega
      omega
    rw [onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_top
      Φ τ x htop]
    simp

/-- **Tasaki §2.5 Theorem 2.3 on-`A` local raising non-positivity**:
including the boundary case where the target local value is already
`N`, the signed single-site raising contribution is non-positive at
every site inside `A`.

This is the weak boundary-inclusive form of
`tasaki23_signed_single_site_raising_component_neg_of_A_true`. -/
theorem tasaki23_signed_single_site_raising_component_nonpos_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) (x : V)
    (hAx : A x = true)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) ≤ 0 := by
  by_cases hx : (τ.1 x).val < N
  · exact le_of_lt
      (tasaki23_signed_single_site_raising_component_neg_of_A_true
        A Φ τ x hx hAx hΦ_pos)
  · have htop : (τ.1 x).val = N := by
      have hle : (τ.1 x).val ≤ N := by
        have := (τ.1 x).isLt
        omega
      omega
    rw [onSiteS_spinSOpPlus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_top
      Φ τ x htop]
    simp

/-- **Tasaki §2.5 Theorem 2.3 off-`A` raised sign-sum bound**:
the filtered sum of signed single-site raising contributions over
sites outside `A` is non-negative.

This is the finite-sum form of
`tasaki23_signed_single_site_raising_component_nonneg_of_A_false`. -/
theorem tasaki23_signed_raising_offA_sum_nonneg
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    0 ≤ ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  apply Finset.sum_nonneg
  intro x hx
  have hAx : A x = false := by
    simpa using (Finset.mem_filter.mp hx).2
  exact tasaki23_signed_single_site_raising_component_nonneg_of_A_false
    A Φ τ x hAx hΦ_pos

/-- **Tasaki §2.5 Theorem 2.3 on-`A` raised sign-sum bound**:
the filtered sum of signed single-site raising contributions over
sites inside `A` is non-positive.

This is the finite-sum form of
`tasaki23_signed_single_site_raising_component_nonpos_of_A_true`. -/
theorem tasaki23_signed_raising_onA_sum_nonpos
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro x hx
  have hAx : A x = true := by
    simpa using (Finset.mem_filter.mp hx).2
  exact tasaki23_signed_single_site_raising_component_nonpos_of_A_true
    A Φ τ x hAx hΦ_pos

/-- **Tasaki §2.5 Theorem 2.3 signed local raising contribution**:
the real signed contribution of the `x`-summand in the raised
site-sum at a target predecessor-sector configuration.

This packages the repeated real expression used to split the raised
site-sum into its off-`A` and on-`A` filtered pieces. -/
noncomputable def tasaki23SignedRaisingSiteContribution
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) (x : V) : ℝ :=
  (marshallSignS A τ.1).re *
    ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
      (magSectorEmbedding Φ)) τ.1).re)

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` raised sign-sum witness**:
if at least one site outside `A` can be raised in the target predecessor
configuration, then the off-`A` filtered signed raising sum is strictly
positive.

This is the raising-direction companion to
`tasaki23_signed_lowering_offA_sum_pos_of_exists_lowerable_offA`. -/
theorem tasaki23_signed_raising_offA_sum_pos_of_exists_raiseable_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hwitness : ∃ x : V, A x = false ∧ (τ.1 x).val < N) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedRaisingSiteContribution A Φ τ x := by
  classical
  obtain ⟨x, hAx, hx⟩ := hwitness
  apply Finset.sum_pos'
  · intro y hy
    unfold tasaki23SignedRaisingSiteContribution
    have hAy : A y = false := by
      simpa using (Finset.mem_filter.mp hy).2
    exact tasaki23_signed_single_site_raising_component_nonneg_of_A_false
      A Φ τ y hAy hΦ_pos
  · refine ⟨x, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hAx⟩
    · unfold tasaki23SignedRaisingSiteContribution
      exact tasaki23_signed_single_site_raising_component_pos_of_A_false
        A Φ τ x hx hAx hΦ_pos

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 off-`A` raiseable witness from vacancy**:
if the total local vacancy on the complement sublattice is positive,
then some site outside `A` is below the top local occupation `N` and
can contribute a strict raised summand. -/
theorem tasaki23_exists_raiseable_offA_of_offA_vacancy_pos
    (A : V → Bool) {M : ℕ} (τ : magConfigS V N M)
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (N - (τ.1 x).val)) :
    ∃ x : V, A x = false ∧ (τ.1 x).val < N := by
  classical
  by_contra hnone
  have hzero :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        (N - (τ.1 x).val)) = 0 := by
    simpa using
      (Finset.sum_eq_zero
        (s := Finset.univ.filter (fun x : V => A x = false))
        (f := fun x : V => N - (τ.1 x).val)
        (by
          intro x hx
          have hAx : A x = false := by
            simpa using (Finset.mem_filter.mp hx).2
          have hxnot : ¬ (τ.1 x).val < N := by
            intro hxlt
            exact hnone ⟨x, hAx, hxlt⟩
          have hxge : N ≤ (τ.1 x).val := by omega
          exact Nat.sub_eq_zero_of_le hxge))
  omega

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` raised sign-sum from
positive off-`A` vacancy**: a positive complement-sublattice vacancy
sum supplies the raiseable witness needed for strict off-`A` raised
signed-sum positivity. -/
theorem tasaki23_signed_raising_offA_sum_pos_of_offA_vacancy_pos
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hΦ_pos : ∀ σ : magConfigS V N (M + 1),
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (N - (τ.1 x).val)) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedRaisingSiteContribution A Φ τ x :=
  tasaki23_signed_raising_offA_sum_pos_of_exists_raiseable_offA
    A Φ τ hΦ_pos
    (tasaki23_exists_raiseable_offA_of_offA_vacancy_pos A τ hoffA_pos)

/-- **Tasaki §2.5 Theorem 2.3 raised site-sum decomposition**:
the full signed raised site-sum is the sum of its off-`A` and on-`A`
filtered signed pieces.

This is the exact Boolean partition needed before comparing the
non-negative off-`A` part with the non-positive on-`A` part. -/
theorem tasaki23_signed_raising_site_sum_eq_offA_add_onA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M) :
    (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23SignedRaisingSiteContribution A Φ τ x) +
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23SignedRaisingSiteContribution A Φ τ x) := by
  classical
  unfold tasaki23SignedRaisingSiteContribution
  rw [Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun x : V => A x = false)
    (f := fun x : V =>
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re))]
  congr 1
  apply Finset.sum_congr
  · ext x
    by_cases hAx : A x = false
    · simp [hAx]
    · cases hA : A x <;> simp [hA] at hAx ⊢
  · intro x _hx
    rfl

/-- **Tasaki §2.5 Theorem 2.3 raised site-sum positivity from
sublattice dominance**: if the negative of the on-`A` signed sum is
strictly smaller than the off-`A` signed sum, then the full signed
raised site-sum is strictly positive.

This is the raising-direction companion to
`tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA`. -/
theorem tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N (M + 1) → ℂ)
    (τ : magConfigS V N M)
    (hdominates :
      -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23SignedRaisingSiteContribution A Φ τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23SignedRaisingSiteContribution A Φ τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  rw [tasaki23_signed_raising_site_sum_eq_offA_add_onA A Φ τ]
  linarith


end LatticeSystem.Quantum
