import LatticeSystem.Quantum.SpinS.Theorem23LocalCoefficientRaisingSource

/-!
# Tasaki §2.5 Theorem 2.3 local predecessor-difference API

This module contains the sublattice coefficient and predecessor
raising-source difference identities downstream of
`Theorem23LocalCoefficientRaisingSource.lean`. The fully threaded unpacked
predecessor-difference callback adapters are isolated in
`Theorem23LocalDifferenceUnpacked.lean`, the lowered site-sum dominance layer
is isolated in `Theorem23LocalDifferenceSiteSum.lean`, the raising-direction
component layer is isolated in `Theorem23LocalDifferenceRaising.lean`, the
raised site-sum contribution/decomposition suffix is isolated in
`Theorem23LocalDifferenceRaisingSiteSum.lean`, and the final
Marshall-positivity wrappers are isolated in
`Theorem23LocalDifferenceMarshall.lean`. The adjacent-sector energy comparison
wrappers downstream of those layers are isolated in
`Theorem23LocalDifferenceEnergy.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 off-`A` lowered sublattice coefficient
component**: the Marshall-signed real component of `Ŝ_¬A^- Φ` at a
target configuration is the off-`A` predecessor-coefficient sum.

This turns the off-sublattice half of the coefficient split into a
statement about the actual complement-sublattice lowering operator. -/
theorem tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (marshallSignS A τ.1).re *
        (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
          (magSectorEmbedding Φ)) τ.1).re =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  rw [sublatticeSpinSOpMinus_complement_mulVec_magSectorEmbedding_apply_eq_offA_site_sum
    A Φ τ.1]
  rw [Complex.re_sum, Finset.mul_sum]
  change
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
      ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x
  exact tasaki23_signed_lowering_offA_sum_eq_coefficient_sum A Φ τ

/-- **Tasaki §2.5 Theorem 2.3 on-`A` lowered sublattice coefficient
component**: the Marshall-signed real component of `Ŝ_A^- Φ` at a
target configuration is the negative of the on-`A`
predecessor-coefficient sum.

This is the operator-level form of the on-sublattice half of the
coefficient split. -/
theorem tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
    {M : ℕ} (A : V → Bool) (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N (M + 1)) :
    (marshallSignS A τ.1).re *
        (((sublatticeSpinSOpMinus N A).mulVec
          (magSectorEmbedding Φ)) τ.1).re =
      -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x := by
  rw [sublatticeSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_onA_site_sum
    A Φ τ.1]
  rw [Complex.re_sum, Finset.mul_sum]
  change
    (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23SignedLoweringSiteContribution A Φ τ x) =
      -∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
        tasaki23LoweringPredecessorSignedCoefficient A Φ τ x
  exact tasaki23_signed_lowering_onA_sum_eq_neg_coefficient_sum A Φ τ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predecessor raising-source difference as a
lowered component**: for a Marshall-signed positive source vector, the
off-`A` minus on-`A` predecessor raising-source difference is exactly the
Marshall-signed real component of the full lowered vector
`Ŝ^-_tot Ψ`.

This identifies the difference-form callback with the operator-level
lowered-vector positivity statement used in the adjacent-sector
comparison. -/
theorem tasaki23_raising_predecessor_source_difference_eq_lowered_marshall_component
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (τ : magConfigS V N (M + 1)) :
    (∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
        tasaki23RaisingPredecessorSourceCoefficient v τ x) -
      (∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
        tasaki23RaisingPredecessorSourceCoefficient v τ x) =
      (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  classical
  let Φ : magConfigS V N M → ℂ :=
    fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)
  have hoff :
      (marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
            (magSectorEmbedding Φ)) τ.1).re =
        ∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
          tasaki23RaisingPredecessorSourceCoefficient v τ x := by
    rw [tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
      A Φ τ]
    rw [show
        (∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) =
        ∑ x ∈ Finset.univ.filter (fun x : V => A x = false),
          tasaki23LoweringPredecessorSignedCoefficient A
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x from by
        rfl]
    rw [
      tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
        A v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
        v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
        v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false)),
      tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false))]
  have hon :
      (marshallSignS A τ.1).re *
          (((sublatticeSpinSOpMinus N A).mulVec
            (magSectorEmbedding Φ)) τ.1).re =
        -∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
          tasaki23RaisingPredecessorSourceCoefficient v τ x := by
    rw [tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
      A Φ τ]
    rw [show
        (∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
          tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) =
        ∑ x ∈ Finset.univ.filter (fun x : V => A x = true),
          tasaki23LoweringPredecessorSignedCoefficient A
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) τ x from by
        rfl]
    rw [
      tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
        A v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
        v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum
        v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_lowerable_positive_source_attach_sum_eq_raising_predecessor_source_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true)),
      tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
        (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true))]
  rw [show
      (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) =
        ((sublatticeSpinSOpMinus N A).mulVec (magSectorEmbedding Φ)) +
          ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
            (magSectorEmbedding Φ)) from by
      rw [totalSpinSOpMinus_eq_sublattice_sum (N := N) A]
      rw [Matrix.add_mulVec]]
  rw [Pi.add_apply, Complex.add_re, mul_add, hon, hoff]
  ring

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered Marshall positivity from
predecessor raising-source differences**: positivity of the off-`A`
minus on-`A` predecessor raising-source difference proves the
Marshall-positive lowered-vector component.

The proof first rewrites the lowerable attached sums as boundary sums
and then applies
`tasaki23_raising_predecessor_source_difference_eq_lowered_marshall_component`.
This connects the real source-weight difference callback to the
lowered-sector Marshall-positivity hypothesis used by the adjacent-sector
energy comparison. -/
theorem tasaki23_lowered_marshall_pos_of_raising_predecessor_source_difference_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (hdiff :
      ∀ τ : magConfigS V N (M + 1),
        0 <
          (((Finset.univ.filter (fun x : V => A x = false)).filter
              (fun x : V => 0 < (τ.1 x).val)).attach.sum
            (fun x =>
              let predVal : Fin (N + 1) :=
                ⟨(τ.1 x.1).val - 1, by omega⟩
              let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
              (spinSOpPlus N predVal (τ.1 x.1)).re *
                v ⟨pred,
                  magSumS_single_site_lowering_predecessor
                    τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) -
            (((Finset.univ.filter (fun x : V => A x = true)).filter
                (fun x : V => 0 < (τ.1 x).val)).attach.sum
              (fun x =>
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x.1).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x.1 predVal
                (spinSOpPlus N predVal (τ.1 x.1)).re *
                  v ⟨pred,
                    magSumS_single_site_lowering_predecessor
                      τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  intro τ
  have hτ := hdiff τ
  rw [
    tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
      (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = false)),
    tasaki23_raising_predecessor_source_attach_sum_eq_boundary_sum
      (V := V) (N := N) v τ (Finset.univ.filter (fun x : V => A x = true)),
    tasaki23_raising_predecessor_source_difference_eq_lowered_marshall_component
      A v τ] at hτ
  exact hτ


end LatticeSystem.Quantum
