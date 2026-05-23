import LatticeSystem.Quantum.SpinS.Theorem23LocalCoefficient

/-!
# Tasaki §2.5 Theorem 2.3 signed-coefficient sum identities

This module contains the signed-coefficient identities split as a stable
suffix from `Theorem23LocalCoefficient.lean`: the Marshall-signed predecessor
coefficient equals the sign-normalized positive-source coefficient, the signed
lowering site-contribution equals plus/minus the predecessor coefficient on the
two sublattices, and the off-`A`/on-`A` filtered signed-lowering sums equal the
corresponding coefficient sums (up to sign). The parent module keeps the
predecessor/coefficient definitions and the positive-source coefficient
theorems.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 signed coefficient as positive-source
coefficient**: for a Marshall-signed real source vector, the
boundary-inclusive signed predecessor coefficient is exactly the
sign-normalized positive-source coefficient. -/
theorem tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source_coefficient
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (x : V) :
    tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x =
      tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x := by
  classical
  by_cases hx : 0 < (τ.1 x).val
  · rw [tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source
      A v τ x hx]
    simp [tasaki23LoweringPredecessorPositiveSourceCoefficient, hx]
  · simp [tasaki23LoweringPredecessorSignedCoefficient,
      tasaki23LoweringPredecessorPositiveSourceCoefficient, hx]

/-- **Tasaki §2.5 Theorem 2.3 signed coefficient sum as positive-source
coefficient sum**: over any finite site set, the Marshall-signed
predecessor coefficient sum for a Marshall-signed real source vector is
the corresponding sign-normalized positive-source coefficient sum. -/
theorem tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) (s : Finset V) :
    (∑ x ∈ s,
      tasaki23LoweringPredecessorSignedCoefficient A
        (fun σ : magConfigS V N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x) =
      ∑ x ∈ s, tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x := by
  apply Finset.sum_congr rfl
  intro x _hx
  exact
    tasaki23_lowering_predecessor_signed_coefficient_eq_positive_source_coefficient
      A v τ x

/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowered contribution split**:
outside `A`, the signed single-site lowering contribution is exactly
the boundary-inclusive signed predecessor coefficient.

This packages the off-`A` coefficient identity in a form that can be
summed without carrying a separate lowerability proof for every site. -/
theorem tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hAx : A x = false) :
    tasaki23SignedLoweringSiteContribution A Φ τ x =
      tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  classical
  by_cases hx : 0 < (τ.1 x).val
  · simpa [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient, hx]
      using
        tasaki23_signed_single_site_lowering_component_eq_of_A_false
          A Φ τ x hx hAx
  · have hzero : (τ.1 x).val = 0 := by omega
    rw [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient]
    rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
      Φ τ x hzero]
    simp [hx]

/-- **Tasaki §2.5 Theorem 2.3 on-`A` lowered contribution split**:
inside `A`, the signed single-site lowering contribution is the
negative of the boundary-inclusive signed predecessor coefficient.

This is the on-`A` companion to
`tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false`
and isolates the exact term whose total size must be dominated by the
off-`A` contribution in the final lowered Marshall-positivity proof. -/
theorem tasaki23_signed_lowering_site_contribution_eq_neg_coefficient_of_A_true
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) (x : V)
    (hAx : A x = true) :
    tasaki23SignedLoweringSiteContribution A Φ τ x =
      -tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  classical
  by_cases hx : 0 < (τ.1 x).val
  · simpa [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient, hx]
      using
        tasaki23_signed_single_site_lowering_component_eq_neg_of_A_true
          A Φ τ x hx hAx
  · have hzero : (τ.1 x).val = 0 := by omega
    rw [tasaki23SignedLoweringSiteContribution,
      tasaki23LoweringPredecessorSignedCoefficient]
    rw [onSiteS_spinSOpMinus_mulVec_magSectorEmbedding_apply_eq_zero_of_target_zero
      Φ τ x hzero]
    simp [hx]

/-- **Tasaki §2.5 Theorem 2.3 off-`A` coefficient-sum split**:
the off-`A` filtered signed lowering sum is exactly the corresponding
sum of boundary-inclusive predecessor coefficients.

This is the finite-sum form of
`tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false`
and is the off-`A` side of the coefficient-level dominance comparison. -/
theorem tasaki23_signed_lowering_offA_sum_eq_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
    ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  apply Finset.sum_congr rfl
  intro x hx
  have hAx : A x = false := by
    simpa using (Finset.mem_filter.mp hx).2
  exact tasaki23_signed_lowering_site_contribution_eq_coefficient_of_A_false
    A Φ τ x hAx

/-- **Tasaki §2.5 Theorem 2.3 on-`A` coefficient-sum split**:
the on-`A` filtered signed lowering sum is the negative of the
corresponding boundary-inclusive predecessor coefficient sum.

This is the finite-sum form of
`tasaki23_signed_lowering_site_contribution_eq_neg_coefficient_of_A_true`
and isolates the negative sublattice contribution that must be
controlled in the final lowered Marshall-positivity proof. -/
theorem tasaki23_signed_lowering_onA_sum_eq_neg_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
    -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  calc
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
        ∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          -tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
          apply Finset.sum_congr rfl
          intro x hx
          have hAx : A x = true := by
            simpa using (Finset.mem_filter.mp hx).2
          exact
            tasaki23_signed_lowering_site_contribution_eq_neg_coefficient_of_A_true
              A Φ τ x hAx
    _ = -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
          rw [Finset.sum_neg_distrib]

end LatticeSystem.Quantum
