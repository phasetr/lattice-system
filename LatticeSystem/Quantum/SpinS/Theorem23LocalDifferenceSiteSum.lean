import LatticeSystem.Quantum.SpinS.Theorem23LocalDifference

/-!
# Tasaki §2.5 Theorem 2.3 local-difference site-sum API

This module contains the strict off-`A` lowering witnesses and lowered
site-sum dominance bridges split from `Theorem23LocalDifference.lean`.
The predecessor-difference callbacks remain in `Theorem23LocalDifference.lean`,
while final Marshall-positivity wrappers are isolated in
`Theorem23LocalDifferenceMarshall.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Lowered site-sum dominance -/

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` lowered sign-sum witness**:
if at least one site outside `A` can be lowered in the target
configuration, then the off-`A` filtered signed lowering sum is strictly
positive.

This is the strict companion to
`tasaki23_signed_lowering_offA_sum_nonneg`: all off-`A` terms are
non-negative, and the witness site contributes strictly positively. -/
theorem tasaki23_signed_lowering_offA_sum_pos_of_exists_lowerable_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hwitness : ∃ x : V, A x = false ∧ 0 < (τ.1 x).val) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x := by
  classical
  obtain ⟨x, hAx, hx⟩ := hwitness
  apply Finset.sum_pos'
  · intro y hy
    unfold tasaki23SignedLoweringSiteContribution
    have hAy : A y = false := by
      simpa using (Finset.mem_filter.mp hy).2
    exact tasaki23_signed_single_site_lowering_component_nonneg_of_A_false
      A Φ τ y hAy hΦ_pos
  · refine ⟨x, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hAx⟩
    · unfold tasaki23SignedLoweringSiteContribution
      exact tasaki23_signed_single_site_lowering_component_pos_of_A_false
        A Φ τ x hx hAx hΦ_pos

omit [DecidableEq V] in
/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowerable witness from occupation**:
if the total local occupation on the complement sublattice is positive,
then some site outside `A` has positive local occupation and can
contribute a strict lowered summand. -/
theorem tasaki23_exists_lowerable_offA_of_offA_occupation_pos
    (A : V → Bool) {M : ℕ} (τ : magConfigS V N (M + 1))
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (τ.1 x).val) :
    ∃ x : V, A x = false ∧ 0 < (τ.1 x).val := by
  classical
  by_contra hnone
  have hzero :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (τ.1 x).val) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hAx : A x = false := by
      simpa using (Finset.mem_filter.mp hx).2
    have hxzero : ¬ 0 < (τ.1 x).val := by
      intro hxpos
      exact hnone ⟨x, hAx, hxpos⟩
    omega
  omega

/-- **Tasaki §2.5 Theorem 2.3 strict off-`A` lowered sign-sum from
positive off-`A` occupation**: a positive complement-sublattice
occupation sum supplies the lowerable witness needed for strict
off-`A` lowered signed-sum positivity. -/
theorem tasaki23_signed_lowering_offA_sum_pos_of_offA_occupation_pos
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hΦ_pos : ∀ σ : magConfigS V N M,
      0 < (marshallSignS A σ.1).re * (Φ σ).re)
    (hoffA_pos :
      0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)), (τ.1 x).val) :
    0 < ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x :=
  tasaki23_signed_lowering_offA_sum_pos_of_exists_lowerable_offA
    A Φ τ hΦ_pos
    (tasaki23_exists_lowerable_offA_of_offA_occupation_pos A τ hoffA_pos)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum decomposition**:
the full signed lowered site-sum is the sum of its off-`A` and on-`A`
filtered signed pieces.

This is the exact Boolean partition needed before comparing the
non-negative off-`A` part with the non-positive on-`A` part. -/
theorem tasaki23_signed_lowering_site_sum_eq_offA_add_onA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) =
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23SignedLoweringSiteContribution A Φ τ x) +
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23SignedLoweringSiteContribution A Φ τ x) := by
  classical
  unfold tasaki23SignedLoweringSiteContribution
  rw [Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun x : V => A x = false)
    (f := fun x : V =>
      (marshallSignS A τ.1).re *
        ((((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re))]
  congr 1
  apply Finset.sum_congr
  · ext x
    by_cases hAx : A x = false
    · simp [hAx]
    · cases hA : A x <;> simp [hA] at hAx ⊢
  · intro x _hx
    rfl

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from
sublattice dominance**: if the negative of the on-`A` signed sum is
strictly smaller than the off-`A` signed sum, then the full signed
lowered site-sum is strictly positive.

This packages the remaining dominance obligation in the site-sum proof. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23SignedLoweringSiteContribution A Φ τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23SignedLoweringSiteContribution A Φ τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  rw [tasaki23_signed_lowering_site_sum_eq_offA_add_onA A Φ τ]
  linarith

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from
coefficient dominance**: if the on-`A` predecessor-coefficient sum is
strictly smaller than the off-`A` predecessor-coefficient sum, then
the full signed lowered site-sum is strictly positive.

This rewrites the earlier signed-contribution dominance callback using
the coefficient-sum split, leaving the remaining proof obligation in
the direct coefficient form. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
      A Φ τ (by
        rw [tasaki23_signed_lowering_onA_sum_eq_neg_coefficient_sum A Φ τ,
          tasaki23_signed_lowering_offA_sum_eq_coefficient_sum A Φ τ]
        simpa using hdominates)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from
positive-source coefficient dominance**: after cancelling the Marshall
signs in the local predecessor coefficients, it is enough to compare the
positive-source coefficient sums over the two sublattices. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_positive_source_coefficient_lt
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA
      A
      (fun σ : magConfigS V N M =>
        (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ
      (by
        rw [
          tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
            A v τ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
            A v τ (Finset.univ.filter (fun x : V => A x = false))]
        exact hdominates)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from lowerable
positive-source coefficient dominance**: after discarding the boundary
sites where the successor configuration cannot be lowered, dominance of
the remaining positive-source predecessor coefficient sums still implies
strict lowered site-sum positivity. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_positive_source_lowerable_coefficient_lt
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
          (fun x : V => 0 < (τ.1 x).val)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
        ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
          (fun x : V => 0 < (τ.1 x).val)),
          tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_positive_source_coefficient_lt
      A v τ (by
        rw [
          tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
            v τ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
            v τ (Finset.univ.filter (fun x : V => A x = false))]
        exact hdominates)

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from sublattice
component dominance**: if the negative Marshall-signed `Ŝ_A^-` component
is strictly smaller than the Marshall-signed `Ŝ_¬A^-` component, then the
full signed lowered site-sum is strictly positive.

This is the operator-component form of
`tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA`. -/
theorem tasaki23_signed_lowering_site_sum_pos_of_sublattice_component_lt
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1))
    (hdominates :
      -((marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N A).mulVec
            (magSectorEmbedding Φ)) τ.1).re) <
        (marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec
            (magSectorEmbedding Φ)) τ.1).re) :
    0 < (marshallSignS A τ.1).re *
      (∑ x : V,
        (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
          (magSectorEmbedding Φ)) τ.1).re) := by
  exact
    tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA
      A Φ τ (by
        have honA :=
          tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
            A Φ τ
        have hoffA :=
          tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
            A Φ τ
        rw [← hoffA]
        rw [← show
          -((marshallSignS A τ.1).re *
            (((sublatticeSpinSOpMinus N A).mulVec
              (magSectorEmbedding Φ)) τ.1).re) =
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A Φ τ x from by
                rw [honA]
                simp]
        exact hdominates)

end LatticeSystem.Quantum
