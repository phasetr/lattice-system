import LatticeSystem.Quantum.SpinS.Theorem23LocalDifference
import LatticeSystem.Quantum.SpinS.Theorem23LocalLoweringPositivity

/-!
# Tasaki §2.5 Theorem 2.3 local-difference raising API

This module contains the raising-direction single-site component API split from
`Theorem23LocalDifference.lean`. The lowered predecessor-difference API
remains in `Theorem23LocalDifference.lean`, the unpacked
predecessor-difference callback adapters are isolated in
`Theorem23LocalDifferenceUnpacked.lean`, the lowered site-sum dominance API is
isolated in `Theorem23LocalDifferenceSiteSum.lean`, and final
Marshall-positivity wrappers are isolated in
`Theorem23LocalDifferenceMarshall.lean`. The strict raised site-sum
contribution/decomposition suffix is isolated in
`Theorem23LocalDifferenceRaisingSiteSum.lean`. This module keeps the raw
single-site raising component formulas; the single-site raising
positivity/negativity, non-negativity/non-positivity, and off-`A`/on-`A`
sign-sum bounds are split into
`Theorem23LocalDifferenceRaisingPositivity.lean`.

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

end LatticeSystem.Quantum
