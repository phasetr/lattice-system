import LatticeSystem.Quantum.SpinS.Theorem23LocalLowering

/-!
# Tasaki §2.5 Theorem 2.3 local lowering sign-sum API

This module contains the weak boundary-inclusive sign bounds and the
off-`A`/on-`A` filtered sign-sum bounds for the local lowering component
API used in Tasaki §2.5 Theorem 2.3. It sits downstream of
`Theorem23LocalLowering.lean`, which keeps the strict single-site
component formulas and Marshall sign identities.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Boundary-inclusive lowering sign sums -/

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
