import LatticeSystem.Quantum.SpinS.Theorem23OutsideGroundPredecessor
import LatticeSystem.Quantum.SpinS.Theorem23PredictedSourceWeight
import LatticeSystem.Quantum.SpinS.Theorem23LocalCoefficientRaisingSource

/-!
# Tasaki §2.5 Theorem 2.3 predecessor raising-source final wrappers

This module contains the real predecessor source-weight and raising-source
final-wrapper suffix split from `Theorem23OutsideGroundPredecessor.lean`. The
base predecessor module keeps the source-weight, positive-source, lowerable,
and explicit lowerable final-wrapper layers, while this module packages the
real source-weight and raising-source boundaries consumed by the
predecessor-difference tail.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from real predecessor
source-weight data**: this threads the real part of the predecessor
source-weight equality into the explicit lowerable positive-source
coefficient callback.

The wrapper derives the real predecessor equality from the older complex
predecessor-specialized source-weight identity using
`tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_re_eq`,
then reuses the explicit lowerable positive-source callback boundary. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (∀ τ : magConfigS V N (M + 1), ∀ x : V,
              ∀ hx : 0 < (τ.1 x).val,
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred).re =
                  ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
                      2 *
                        ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                            ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
                          (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                            ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
                    ((marshallSignS A pred).re *
                      v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              (((Finset.univ.filter (fun x : V => A x = true)).filter
                    (fun x : V => 0 < (τ.1 x).val)).attach.sum
                  (fun x =>
                    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                      v τ x.1 ((Finset.mem_filter.mp x.2).2))) <
                (((Finset.univ.filter (fun x : V => A x = false)).filter
                    (fun x : V => 0 < (τ.1 x).val)).attach.sum
                  (fun x =>
                    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                      v τ x.1 ((Finset.mem_filter.mp x.2).2))))
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        exact
          hsource_unpacked_reembedded_real_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt
            hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred
            (by
              intro τ x hx
              exact
                tasaki23_cross_ladder_reembedded_source_weight_lowering_predecessor_re_eq
                  (V := V) A N hΨ_eq τ x hx (hpred τ x hx))
            hA_A hA_B hA_mag hB_A hB_B hB_mag τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor
raising-source sums**: this threads the real predecessor source-weight
data into a callback stated directly as strict dominance of the
predecessor raising-source sums.

The wrapper uses
`tasaki23_lowerable_positive_source_attach_sum_lt_of_raising_predecessor_source_sum_lt`
to recover the explicit lowerable positive-source coefficient comparison
expected by the preceding real predecessor callback. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_raising_source_sum_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_reembedded_real_source_weight_predecessor_raising_source_sum_lt :
      ∀ {M : ℕ},
        M ∈ tasaki23GroundStateSectors (V := V) A N →
        M <
          max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N →
        ∀ {μ : ℝ} {v : magConfigS V N M → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          ∀ Ψ : (V → Fin (N + 1)) → ℂ,
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N →
            (∀ τ : magConfigS V N (M + 1), ∀ x : V,
              ∀ hx : 0 < (τ.1 x).val,
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred).re =
                  ((bipartiteToyMinEnergyPredicted (Λ := V) A N).re -
                      2 *
                        ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                            ((N : ℝ) / 2 - ((pred y).val : ℝ))) *
                          (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                            ((N : ℝ) / 2 - ((pred y).val : ℝ))))) *
                    ((marshallSignS A pred).re *
                      v ⟨pred, magSumS_single_site_lowering_predecessor τ x hx⟩)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              (((Finset.univ.filter (fun x : V => A x = true)).filter
                    (fun x : V => 0 < (τ.1 x).val)).attach.sum
                  (fun x =>
                    let predVal : Fin (N + 1) :=
                      ⟨(τ.1 x.1).val - 1, by omega⟩
                    let pred : V → Fin (N + 1) :=
                      Function.update τ.1 x.1 predVal
                    (spinSOpPlus N predVal (τ.1 x.1)).re *
                      v ⟨pred,
                        magSumS_single_site_lowering_predecessor
                          τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)) <
                (((Finset.univ.filter (fun x : V => A x = false)).filter
                    (fun x : V => 0 < (τ.1 x).val)).attach.sum
                  (fun x =>
                    let predVal : Fin (N + 1) :=
                      ⟨(τ.1 x.1).val - 1, by omega⟩
                    let pred : V → Fin (N + 1) :=
                      Function.update τ.1 x.1 predVal
                    (spinSOpPlus N predVal (τ.1 x.1)).re *
                      v ⟨pred,
                        magSumS_single_site_lowering_predecessor
                          τ x.1 ((Finset.mem_filter.mp x.2).2)⟩)))
    (hsector_min :
      ∀ {μ : ℝ},
        (∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
          ∃ v : magConfigS V N M → ℝ,
            μ < c ∧ (∀ τ, 0 < v τ) ∧
            (heisenbergHamiltonianS J N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
              (μ : ℂ) • magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) →
        ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
          ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
            Φ ≠ 0 →
            (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
              (μ' : ℂ) • Φ →
            μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        exact
          tasaki23_lowerable_positive_source_attach_sum_lt_of_raising_predecessor_source_sum_lt
            (V := V) (N := N) A v τ
            (hsource_unpacked_reembedded_real_source_weight_predecessor_raising_source_sum_lt
              hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
              hB_A hB_B hB_mag τ))
      hsector_min

end LatticeSystem.Quantum
