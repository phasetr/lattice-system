import LatticeSystem.Quantum.SpinS.Theorem23OutsideGroundCrossLadderReembedded
import LatticeSystem.Quantum.SpinS.Theorem23PredictedSourceWeight
import LatticeSystem.Quantum.SpinS.Theorem23LocalCoefficient

/-!
# Tasaki §2.5 Theorem 2.3 outside-ground predecessor final wrappers

This module contains the predecessor-specialized source-weight,
positive-source, lowerable, and explicit lowerable final-wrapper chain for
the Tasaki §2.5 Theorem 2.3 proof chain. The real source-weight and
raising-source final-wrapper suffix is split further into
`Theorem23OutsideGroundPredecessorRaising.lean`, so the predecessor-difference
tail can elaborate without keeping the whole predecessor API in one module.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor-specialized
source-weight sums**: this threads the scalar re-embedded source-weight
identity after specializing it to the lowering predecessor configuration
attached to each successor site.

The callback receives exactly the local source-weight identity at the
predecessor used by `tasaki23LoweringPredecessorSignedCoefficient`,
together with the four explicit sublattice-Casimir equations and the two
successor-sector `magSubspaceS` support facts for the lowered components. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_reembedded_source_weight_predecessor_coefficient_lt :
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
              0 < (τ.1 x).val →
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
                  (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                    (2 : ℂ) *
                      ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
                        (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred) →
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
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorSignedCoefficient A
                  (fun τ : magConfigS V N M =>
                    (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  tasaki23LoweringPredecessorSignedCoefficient A
                    (fun τ : magConfigS V N M =>
                      (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x)
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
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred _hraw hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hpred :
            ∀ τ : magConfigS V N (M + 1), ∀ x : V,
              0 < (τ.1 x).val →
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
                  (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                    (2 : ℂ) *
                      ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
                        (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred := by
          intro τ x hx
          exact
            tasaki23_cross_ladder_reembedded_source_weight_eq_lowering_predecessor_of_predictedGS
              (V := V) A N hΨ_pred hA_mag hB_mag τ x hx
        exact
          hsource_unpacked_reembedded_source_weight_predecessor_coefficient_lt
            hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
            hB_A hB_B hB_mag τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from predecessor positive-source
coefficient sums**: this threads the predecessor-specialized source-weight
identity while stating the remaining local dominance callback in the
sign-normalized positive-source coefficient form.

The wrapper rewrites the positive-source coefficient sums back to the
Marshall-signed predecessor coefficient sums consumed by the previous
predecessor-specialized final wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_positive_source_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_reembedded_source_weight_predecessor_positive_source_coefficient_lt :
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
              0 < (τ.1 x).val →
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
                  (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                    (2 : ℂ) *
                      ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
                        (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred) →
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
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x)
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
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hpos :=
          hsource_unpacked_reembedded_source_weight_predecessor_positive_source_coefficient_lt
            hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
            hB_A hB_B hB_mag τ
        rw [
          tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
            A v τ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23_lowering_predecessor_coefficient_sum_eq_positive_source_sum
            A v τ (Finset.univ.filter (fun x : V => A x = false))]
        exact hpos)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from lowerable predecessor
positive-source coefficient sums**: this threads the
predecessor-specialized source-weight identity while allowing the final
local callback to compare only lowerable sites of the successor
configuration.

The wrapper rewrites the unfiltered positive-source coefficient sums of
the previous final wrapper by
`tasaki23_positive_source_coefficient_sum_eq_lowerable_sum`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_lowerable_positive_source_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_reembedded_source_weight_predecessor_lowerable_positive_source_coefficient_lt :
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
              0 < (τ.1 x).val →
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
                  (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                    (2 : ℂ) *
                      ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
                        (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred) →
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
              (∑ x ∈ ((Finset.univ.filter (fun x : V => A x = true)).filter
                  (fun x : V => 0 < (τ.1 x).val)),
                  tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x) <
                ∑ x ∈ ((Finset.univ.filter (fun x : V => A x = false)).filter
                  (fun x : V => 0 < (τ.1 x).val)),
                  tasaki23LoweringPredecessorPositiveSourceCoefficient v τ x)
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
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_positive_source_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hlowerable :=
          hsource_unpacked_reembedded_source_weight_predecessor_lowerable_positive_source_coefficient_lt
            hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
            hB_A hB_B hB_mag τ
        rw [
          tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
            v τ (Finset.univ.filter (fun x : V => A x = true)),
          tasaki23_positive_source_coefficient_sum_eq_lowerable_sum
            v τ (Finset.univ.filter (fun x : V => A x = false))]
        exact hlowerable)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from explicit lowerable
positive-source coefficient sums**: this threads the predecessor-specialized
source-weight identity while asking the final local callback only for
attached sums of the explicit lowerable predecessor coefficients.

The wrapper converts those attached sums back to the lowerable-filtered
boundary-inclusive sums by
`tasaki23_positive_source_lowerable_filter_sum_eq_lowerable_attach_sum`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_reembedded_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt :
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
              0 < (τ.1 x).val →
                let predVal : Fin (N + 1) :=
                  ⟨(τ.1 x).val - 1, by omega⟩
                let pred : V → Fin (N + 1) := Function.update τ.1 x predVal
                (∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N (fun y => ! A y)).mulVec Ψ)))) pred) +
                  ∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                    ((onSiteS y (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                      (magSectorEmbedding
                        (magSectorRestriction (M := M + 1)
                          ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) pred =
                  (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                    (2 : ℂ) *
                      ((∑ y ∈ (Finset.univ.filter (fun y : V => A y = true)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))) *
                        (∑ y ∈ (Finset.univ.filter (fun y : V => A y = false)),
                          ((N : ℂ) / 2 - ((pred y).val : ℂ))))) * Ψ pred) →
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
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_predecessor_lowerable_positive_source_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        exact
          tasaki23_positive_source_lowerable_coefficient_lt_of_attach_sum_lt
            A v τ
            (hsource_unpacked_reembedded_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt
              hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
              hB_A hB_B hB_mag τ))
      hsector_min

end LatticeSystem.Quantum
