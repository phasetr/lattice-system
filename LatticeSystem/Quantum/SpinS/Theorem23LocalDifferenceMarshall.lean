import LatticeSystem.Quantum.SpinS.Theorem23LocalDifferenceRaisingSiteSum
import LatticeSystem.Quantum.SpinS.Theorem23LocalDifferenceSiteSum

/-!
# Tasaki §2.5 Theorem 2.3 local-difference Marshall wrappers

This module contains the final lowered/raised Marshall-positivity wrappers
split from `Theorem23LocalDifference.lean`. It depends on the lowered
site-sum API in `Theorem23LocalDifferenceSiteSum.lean` and the
raised site-sum API in `Theorem23LocalDifferenceRaisingSiteSum.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
site-sum positivity**: to prove the Marshall positivity required by the
adjacent-sector comparison, it suffices to prove the corresponding
strict positivity after expanding `Ŝ^-_tot` as the real part of the sum
of single-site lowering contributions.

This is the bridge from the global lowered-vector hypothesis to the
sitewise predecessor analysis used in Tasaki's ladder comparison. -/
theorem tasaki23_lowered_marshall_pos_of_site_sum_pos
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N M → ℂ)
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding Φ)) τ.1).re)) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  intro τ
  rw [totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum Φ τ.1]
  simpa [map_sum] using hlowered_site_sum_pos τ

/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from
vector Marshall positivity**: the vector-level Marshall positivity of
`S^-_{\mathrm{tot}} Φ` implies the corresponding strict site-sum
positivity after expanding the total lowering operator into its
single-site summands.

Together with `tasaki23_lowered_marshall_pos_of_site_sum_pos`, this
identifies the direct site-sum callback used by the interval chain with
the natural Marshall-positivity statement for the lowered ladder image. -/
theorem tasaki23_lowered_site_sum_pos_of_marshall_pos
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N M → ℂ)
    (hlowered_marshall_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) := by
  intro τ
  have hτ := hlowered_marshall_pos τ
  rw [totalSpinSOpMinus_mulVec_magSectorEmbedding_apply_eq_site_sum Φ τ.1] at hτ
  simpa [map_sum] using hτ

/-- **Tasaki §2.5 Theorem 2.3 source-form lowered site-sum positivity from
lowered Marshall positivity**: for a Marshall-signed positive real source
representative, vector-level Marshall positivity of the total lowered
image supplies the explicit single-site lowering sum positivity consumed
by the adjacent-sector chain.

This is the source-representative specialization of
`tasaki23_lowered_site_sum_pos_of_marshall_pos`, matching the output shape
of the predecessor raising-source difference bridge. -/
theorem tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos
    {M : ℕ} (A : V → Bool) (v : magConfigS V N M → ℝ)
    (hlowered_marshall_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun σ : magConfigS V N M =>
                (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (fun σ : magConfigS V N M =>
                (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  exact
    tasaki23_lowered_site_sum_pos_of_marshall_pos (V := V) (N := N) A
      (fun σ : magConfigS V N M =>
        (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
      hlowered_marshall_pos

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered site-sum positivity from predecessor
raising-source positive differences**: for a Marshall-signed positive
source representative, positivity of the off-`A` minus on-`A` predecessor
raising-source difference supplies the strict single-site lowered sum
positivity consumed by the adjacent-sector chain.

This composes
`tasaki23_lowered_marshall_pos_of_raising_predecessor_source_difference_pos`
with the source-form site-sum bridge
`tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos`. -/
theorem tasaki23_lowered_site_sum_pos_of_raising_predecessor_source_difference_pos
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
        (∑ x : V,
          (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding
              (fun σ : magConfigS V N M =>
                (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re) := by
  exact
    tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos A v
      (tasaki23_lowered_marshall_pos_of_raising_predecessor_source_difference_pos
        (V := V) (N := N) A v hdiff)

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
sublattice dominance**: a pointwise dominance of the off-`A` signed
lowered sum over the negative on-`A` signed sum implies the
Marshall-positive lowered-vector hypothesis.

This feeds the dominance bridge into
`tasaki23_lowered_marshall_pos_of_site_sum_pos`. -/
theorem tasaki23_lowered_marshall_pos_of_onA_neg_lt_offA
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N M → ℂ)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedLoweringSiteContribution A Φ τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedLoweringSiteContribution A Φ τ x) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  exact tasaki23_lowered_marshall_pos_of_site_sum_pos A Φ
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
        A Φ τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
coefficient dominance**: a pointwise coefficient dominance of the
off-`A` lowered predecessor sum over the on-`A` lowered predecessor sum
implies the Marshall-positive lowered-vector hypothesis.

This is the coefficient-level version of
`tasaki23_lowered_marshall_pos_of_onA_neg_lt_offA`, using the
coefficient-sum split to remove the signed-contribution notation from
the remaining callback. -/
theorem tasaki23_lowered_marshall_pos_of_onA_coefficient_lt_offA
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N M → ℂ)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23LoweringPredecessorSignedCoefficient A Φ τ x) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  exact tasaki23_lowered_marshall_pos_of_site_sum_pos A Φ
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_onA_coefficient_lt_offA
        A Φ τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
positive-source coefficient dominance**: a pointwise dominance of the
sign-normalized positive-source predecessor coefficient sum over `A` by
the corresponding sum over `¬A` implies Marshall positivity of the
lowered vector. -/
theorem tasaki23_lowered_marshall_pos_of_positive_source_coefficient_lt
    (A : V → Bool) {M : ℕ} (v : magConfigS V N M → ℝ)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  exact tasaki23_lowered_marshall_pos_of_site_sum_pos A
    (fun σ : magConfigS V N M =>
      (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_positive_source_coefficient_lt
        A v τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
lowerable positive-source coefficient dominance**: it is enough to prove
the positive-source coefficient dominance after restricting both
sublattice sums to sites where the successor configuration can be
lowered. -/
theorem tasaki23_lowered_marshall_pos_of_positive_source_lowerable_coefficient_lt
    (A : V → Bool) {M : ℕ} (v : magConfigS V N M → ℝ)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
          ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
            (fun x : V => 0 < (τ.1 x).val)),
            tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun σ : magConfigS V N M =>
              (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))) τ.1).re := by
  exact tasaki23_lowered_marshall_pos_of_site_sum_pos A
    (fun σ : magConfigS V N M =>
      (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_positive_source_lowerable_coefficient_lt
        A v τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 lowered-vector Marshall positivity from
sublattice component dominance**: a pointwise operator-level dominance
of the Marshall-signed `Ŝ_¬A^-` component over the negative
Marshall-signed `Ŝ_A^-` component implies the Marshall-positive
lowered-vector hypothesis.

This is the sublattice-operator version of
`tasaki23_lowered_marshall_pos_of_onA_coefficient_lt_offA`. -/
theorem tasaki23_lowered_marshall_pos_of_sublattice_component_lt
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N M → ℂ)
    (hdominates :
      ∀ τ : magConfigS V N (M + 1),
        -((marshallSignS A τ.1).re *
            (((sublatticeSpinSOpMinus N A).mulVec
              (magSectorEmbedding Φ)) τ.1).re) <
          (marshallSignS A τ.1).re *
            (((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec
              (magSectorEmbedding Φ)) τ.1).re) :
    ∀ τ : magConfigS V N (M + 1),
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  exact tasaki23_lowered_marshall_pos_of_site_sum_pos A Φ
    (fun τ =>
      tasaki23_signed_lowering_site_sum_pos_of_sublattice_component_lt
        A Φ τ (hdominates τ))

/-- **Tasaki §2.5 Theorem 2.3 raised-vector Marshall positivity from
site-sum positivity**: to prove the Marshall positivity required by the
raising-direction adjacent-sector comparison, it suffices to prove the
corresponding strict positivity after expanding `Ŝ^+_tot` as the real
part of the sum of single-site raising contributions.

This is the raising-direction companion to
`tasaki23_lowered_marshall_pos_of_site_sum_pos`. -/
theorem tasaki23_raised_marshall_pos_of_site_sum_pos
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ)
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding Φ)) τ.1).re)) :
    ∀ τ : magConfigS V N M,
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  intro τ
  rw [totalSpinSOpPlus_mulVec_magSectorEmbedding_apply_eq_site_sum Φ τ.1]
  simpa [map_sum] using hraised_site_sum_pos τ

/-- **Tasaki §2.5 Theorem 2.3 raised site-sum positivity from
vector Marshall positivity**: the vector-level Marshall positivity of
`S^+_{\mathrm{tot}} Φ` implies the corresponding strict site-sum
positivity after expanding the total raising operator into its
single-site summands.

This is the raising-direction companion to
`tasaki23_lowered_site_sum_pos_of_marshall_pos`. -/
theorem tasaki23_raised_site_sum_pos_of_marshall_pos
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ)
    (hraised_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) :
    ∀ τ : magConfigS V N M,
      0 < (marshallSignS A τ.1).re *
        (∑ x : V,
          (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
            (magSectorEmbedding Φ)) τ.1).re) := by
  intro τ
  have hτ := hraised_marshall_pos τ
  rw [totalSpinSOpPlus_mulVec_magSectorEmbedding_apply_eq_site_sum Φ τ.1] at hτ
  simpa [map_sum] using hτ

/-- **Tasaki §2.5 Theorem 2.3 raised-vector Marshall positivity from
sublattice dominance**: a pointwise dominance of the off-`A` signed
raised sum over the negative on-`A` signed sum implies the
Marshall-positive raised-vector hypothesis.

This feeds the raising-direction dominance bridge into
`tasaki23_raised_marshall_pos_of_site_sum_pos`. -/
theorem tasaki23_raised_marshall_pos_of_onA_neg_lt_offA
    (A : V → Bool) {M : ℕ} (Φ : magConfigS V N (M + 1) → ℂ)
    (hdominates :
      ∀ τ : magConfigS V N M,
        -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
            tasaki23SignedRaisingSiteContribution A Φ τ x) <
          ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
            tasaki23SignedRaisingSiteContribution A Φ τ x) :
    ∀ τ : magConfigS V N M,
      0 < (marshallSignS A τ.1).re *
        (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re := by
  exact tasaki23_raised_marshall_pos_of_site_sum_pos A Φ
    (fun τ =>
      tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
        A Φ τ (hdominates τ))


end LatticeSystem.Quantum
