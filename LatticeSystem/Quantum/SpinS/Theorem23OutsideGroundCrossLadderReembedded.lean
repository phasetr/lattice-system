import LatticeSystem.Quantum.SpinS.Theorem23OutsideGroundCrossLadderUnpacked

/-!
# Tasaki §2.5 Theorem 2.3 re-embedded cross-ladder final wrappers

This module contains the re-embedded cross-ladder and source-weight
final-wrapper suffix split from `Theorem23OutsideGroundCrossLadder.lean`. The
base cross-ladder module keeps the sublattice-component, joint-component,
lowered-joint, and packed cross-ladder final-wrapper layers, the unpacked
callback boundary is isolated in `Theorem23OutsideGroundCrossLadderUnpacked.lean`,
and this module packages the re-embedded source-sector final boundaries consumed
by the predecessor-specialized tail.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from re-embedded cross-ladder
source-sector site sums**: the final theorem boundary may consume the
remaining local comparison after the predicted-GS cross-ladder identity
has already been evaluated at source-sector configurations and rewritten
through the successor-sector restrictions of the two lowered components.

This is the direct consumer of
`tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_op3_of_predictedGS`.
The callback receives the pointwise filtered `A`/`¬A` raising sums, plus
the explicit sublattice-Casimir equations for both lowered components. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_reembedded_cross_ladder_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_reembedded_cross_ladder_coefficient_lt :
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
            (∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                  ((2 : ℂ) •
                    (sublatticeSpinSOp3 N A *
                      sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ) σ.1) →
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
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred _hcross hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hsite :
            ∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                  ((2 : ℂ) •
                    (sublatticeSpinSOp3 N A *
                      sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ) σ.1 := by
          intro σ
          exact
            tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_op3_of_predictedGS
              (V := V) A N hΨ_pred hA_mag hB_mag σ
        exact
          hsource_reembedded_cross_ladder_coefficient_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_eq hΨ_pred hsite hA_A hA_B hB_A hB_B τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from re-embedded
source-weight cross-ladder sums**: this strengthens the remaining local
callback boundary by giving it the scalar source-weight form of the
re-embedded cross-ladder equation.

The callback no longer receives the raw `Ŝ_A^3 Ŝ_¬A^3` operator term on
the right-hand side. Instead, the filtered raising sums are equated to
`(E_toy - 2 W_A(σ) W_¬A(σ)) * Ψ σ`, where the two weights are the
source-configuration `S^3` sums over `A` and `¬A`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_reembedded_source_weight_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_reembedded_source_weight_coefficient_lt :
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
            (∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                  (2 : ℂ) *
                    ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))) *
                      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))))) * Ψ σ.1) →
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
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_reembedded_cross_ladder_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hraw hA_A hA_B
          hB_A hB_B τ
        have hsite :
            ∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                  (2 : ℂ) *
                    ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))) *
                      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))))) * Ψ σ.1 := by
          intro σ
          rw [hraw σ]
          rw [Pi.sub_apply, Pi.smul_apply, Matrix.smul_mulVec, Pi.smul_apply]
          rw [sublatticeSpinSOp3_mul_complement_mulVec_apply_eq_onA_offA_weight]
          simp [smul_eq_mul]
          ring_nf
        exact
          hsource_reembedded_source_weight_coefficient_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_eq hΨ_pred hsite hA_A hA_B hB_A hB_B τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from unpacked re-embedded
source-weight cross-ladder sums**: this keeps the successor-sector support
from the unpacked lowered-joint callback while replacing the raw
cross-ladder operator equation by the scalar source-weight form.

The callback receives the pointwise identity
`(E_toy - 2 W_A(σ) W_¬A(σ)) * Ψ σ`, the four explicit sublattice-Casimir
equations, and the two `magSubspaceS` memberships for the lowered
components. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_reembedded_source_weight_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_reembedded_source_weight_coefficient_lt :
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
            (∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                  (2 : ℂ) *
                    ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))) *
                      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))))) * Ψ σ.1) →
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
        have hsite :
            ∀ σ : magConfigS V N M,
              (∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)))) σ.1) +
                ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                  ((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                    (magSectorEmbedding
                      (magSectorRestriction (M := M + 1)
                        ((sublatticeSpinSOpMinus N A).mulVec Ψ)))) σ.1 =
                (bipartiteToyMinEnergyPredicted (Λ := V) A N -
                  (2 : ℂ) *
                    ((∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))) *
                      (∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                        ((N : ℂ) / 2 - ((σ.1 x).val : ℂ))))) * Ψ σ.1 := by
          intro σ
          rw [
            tasaki23_cross_ladder_reembedded_source_site_sum_eq_energy_sub_two_op3_of_predictedGS
              (V := V) A N hΨ_pred hA_mag hB_mag σ]
          rw [Pi.sub_apply, Pi.smul_apply, Matrix.smul_mulVec, Pi.smul_apply]
          rw [sublatticeSpinSOp3_mul_complement_mulVec_apply_eq_onA_offA_weight]
          simp [smul_eq_mul]
          ring_nf
        exact
          hsource_unpacked_reembedded_source_weight_coefficient_lt hM hMlt hμ_lt
            hv_pos hΦ Ψ hΨ_eq hΨ_pred hsite hA_A hA_B hA_mag hB_A hB_B
            hB_mag τ)
      hsector_min

end LatticeSystem.Quantum
