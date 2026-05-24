import LatticeSystem.Quantum.SpinS.Theorem23OutsideGroundCrossLadderLoweredJointCross
import LatticeSystem.Quantum.SpinS.Theorem23IntervalJointUnpacked

/-!
# Tasaki §2.5 Theorem 2.3 unpacked cross-ladder final wrappers

This module contains the unpacked lowered-joint cross-ladder final-wrapper
suffix split from `Theorem23OutsideGroundCrossLadderLoweredJoint.lean`. The
base cross-ladder module keeps the sublattice-component, joint-component, and
joint-coefficient final-wrapper layers, the lowered-joint module keeps the
packed lowered-joint wrappers, and this module packages the unpacked
Casimir/support callback boundary consumed by the re-embedded cross-ladder
tail.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from unpacked lowered joint
cross-ladder data**: the final theorem may consume the local strict
comparison callback after the lowered joint-magnetization memberships
have been unpacked into explicit sublattice-Casimir equations and
successor-sector support.

This is the final-theorem counterpart of
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_predictedGS`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_lowered_joint_cross_ladder_component_lt :
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
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ →
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
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re)
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
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_lowered_joint_cross_ladder_component_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_lowered hB_lowered τ
        have hA_A :=
          tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hA_B :=
          tasaki23_sublatticeSpinSquaredS_complement_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hA_mag :=
          tasaki23_mem_magSubspaceS_of_mem_lowered_joint_magSubspace
            (V := V) A N M hA_lowered
        have hB_A :=
          tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        have hB_B :=
          tasaki23_sublatticeSpinSquaredS_complement_eq_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        have hB_mag :=
          tasaki23_mem_magSubspaceS_of_mem_lowered_joint_magSubspace
            (V := V) A N M hB_lowered
        exact
          hsource_unpacked_lowered_joint_cross_ladder_component_lt hM hMlt hμ_lt
            hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_A hA_B hA_mag hB_A hB_B
            hB_mag τ)
      hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 common-energy chain from unpacked lowered
joint cross-ladder data**: the left-endpoint predicted-GS input together
with the unpacked lowered-joint cross-ladder component callback produces
the named common-energy chain used by outside-sector final wrappers.

This packages the existing interval-chain route and forgets the extra
predicted toy ground-state membership carried by
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_predictedGS`.
-/
theorem
    tasaki23_common_energy_chain_of_left_endpoint_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_lowered_joint_cross_ladder_component_lt :
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
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ →
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
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re) :
    ∃ μ : ℝ, tasaki23CommonEnergyChain (V := V) A J N c μ := by
  obtain ⟨μ, hchain_pred⟩ :=
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_predictedGS
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      hsource_unpacked_lowered_joint_cross_ladder_component_lt
  refine ⟨μ, ?_⟩
  intro M hM
  obtain ⟨v, hμ_lt, hv_pos, hΦ, _hpredictedGS⟩ := hchain_pred M hM
  exact ⟨v, hμ_lt, hv_pos, hΦ⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 unpacked lowered-joint cross-ladder final
boundary with outside-sector ground energies**: this replaces the
sector-minimality callback in the unpacked cross-ladder boundary by the
standard outside-sector ground-energy lower family.

The admissible-sector lower bound is obtained from the common-energy chain
produced by the unpacked cross-ladder callback, while sectors outside
`tasaki23GroundStateSectors` are handled by
`tasaki23OutsideGroundEnergyLowerFamilyCallback`. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_lowered_joint_cross_ladder_component_lt :
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
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ →
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
              ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re)
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      hsource_unpacked_lowered_joint_cross_ladder_component_lt
      (fun {μ} hcommon =>
        tasaki23_sector_minimality_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
          A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
          hc_strict h_intermediate hcommon (houtside_ground_energy_lower hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from unpacked lowered joint
cross-ladder coefficient dominance**: the final theorem boundary can
consume the remaining local comparison as predecessor coefficient
dominance after the unpacked cross-ladder callback receives the explicit
Casimir equations and successor-sector support for both lowered
components.

The proof rewrites coefficient dominance into the strict
Marshall-signed component comparison and applies the unpacked component
wrapper. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_coefficient_lt_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_lowered_joint_cross_ladder_coefficient_lt :
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
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ →
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
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hcoeff :=
          hsource_unpacked_lowered_joint_cross_ladder_coefficient_lt hM hMlt
            hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_A hA_B hA_mag hB_A hB_B
            hB_mag τ
        subst Ψ
        have honA :=
          tasaki23_signed_lowering_onA_sublattice_component_eq_neg_coefficient_sum
            A
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ
        have hoffA :=
          tasaki23_signed_lowering_offA_sublattice_component_eq_coefficient_sum
            A
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ
        rw [honA, hoffA]
        simpa using hcoeff)
          hsector_min

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 unpacked lowered-joint cross-ladder coefficient
boundary with outside-sector ground energies**: this replaces the unpacked
component callback in the outside-sector final wrapper by the coefficient
dominance form.

The coefficient dominance callback is first converted to the unpacked
Marshall-signed component comparison. The resulting common-energy chain is
then combined with `tasaki23OutsideGroundEnergyLowerFamilyCallback` through
the standard outside-sector sector-minimality bridge. -/
theorem
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_coefficient_lt_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hBA :
      (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_predictedGS :
      tasaki23LeftEndpointPredictedGSCallback (V := V) A J N c)
    (hsource_unpacked_lowered_joint_cross_ladder_coefficient_lt :
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
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ →
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
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_left_endpoint_threaded_predictedGS_of_unpacked_lowered_joint_cross_ladder_coefficient_lt_of_sector_minimality
      A N c hBA hsector_nonempty hleft_predictedGS
      hsource_unpacked_lowered_joint_cross_ladder_coefficient_lt
      (fun {μ} hcommon =>
        tasaki23_sector_minimality_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
          A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
          hc_strict h_intermediate hcommon (houtside_ground_energy_lower hcommon))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

end LatticeSystem.Quantum
