import LatticeSystem.Quantum.SpinS.Theorem23IntervalPredictedGS

/-!
# Tasaki §2.5 Theorem 2.3 joint interval-chain API

This module contains the joint-component, lowered-joint, cross-ladder, and
unpacked cross-ladder interval-chain wrappers split from
`Theorem23Interval.lean`. Keeping this suffix separate lets the basic
interval-chain callbacks elaborate without replaying the later cross-ladder
API layer.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 interval chain from joint component
structure**: in the threaded predicted-GS interval induction, the local
sublattice comparison callback receives the propagated predicted-GS
membership and the two lowered-component joint sublattice-Casimir
memberships.

This is the direct consumer-facing form of the PR #3408 joint-eigenspace
bridges: the remaining strict comparison can now assume exactly the
structural facts already proved for `Ŝ_A^- Φ` and `Ŝ_¬A^- Φ`. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_joint_sublattice_component_lt_of_predictedGS
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
    (hsource_joint_sublattice_component_lt :
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
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_sublattice_component_lt_of_predictedGS
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ hpred τ => by
        let Ψ : (V → Fin (N + 1)) → ℂ :=
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        have hΨ_def :
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := rfl
        have hpredΨ :
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
          simpa [Ψ] using hpred
        have hA_joint :
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
          simpa [Ψ] using
            (tasaki23_sublatticeSpinSOpMinus_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
              (V := V) A N hpred)
        have hB_joint :
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
          simpa [Ψ] using
            (tasaki23_sublatticeSpinSOpMinus_complement_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
              (V := V) A N hpred)
        simpa [Ψ] using
          (hsource_joint_sublattice_component_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_def hpredΨ hA_joint hB_joint τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 interval chain from lowered joint
magnetization structure**: in the threaded predicted-GS interval
induction, the local sublattice comparison callback receives the two
lowered components as members of the combined joint-Casimir and
successor-sector subspace.

This is the direct consumer-facing form of
`tasaki23LoweredJointMagSubspace`: the remaining strict comparison can
assume each lowered component carries both the joint maximum
sublattice-Casimir structure and the `M + 1` magnetization support. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_magSubspace_component_lt_of_predictedGS
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
    (hsource_lowered_joint_magSubspace_component_lt :
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
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_sublattice_component_lt_of_predictedGS
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ hpred τ => by
        let Ψ : (V → Fin (N + 1)) → ℂ :=
          magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        have hΨ_def :
            Ψ =
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := rfl
        have hpredΨ :
            Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
          simpa [Ψ] using hpred
        have hA_lowered :
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M := by
          simpa [Ψ] using
            (tasaki23_sublatticeSpinSOpMinus_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
              (V := V) A N hpred)
        have hB_lowered :
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M := by
          simpa [Ψ] using
            (tasaki23_sublatticeSpinSOpMinus_complement_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
              (V := V) A N hpred)
        simpa [Ψ] using
          (hsource_lowered_joint_magSubspace_component_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_def hpredΨ hA_lowered hB_lowered τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 interval chain from lowered joint
magnetization and cross-ladder structure**: in the threaded predicted-GS
interval induction, the local sublattice comparison callback also
receives the raised-lowered cross-ladder identity satisfied by the
source predicted toy ground state.

This sharpens
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_magSubspace_component_lt_of_predictedGS`:
the remaining local comparison can now use the lowered joint
magnetization memberships and the predicted-GS cross-ladder equation in
one callback. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_cross_ladder_component_lt_of_predictedGS
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
    (hsource_lowered_joint_cross_ladder_component_lt :
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
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
              tasaki23LoweredJointMagSubspace (V := V) A N M →
            ∀ τ : magConfigS V N (M + 1),
              -((marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N A).mulVec Ψ) τ.1).re) <
                (marshallSignS A τ.1).re *
                  (((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ)
                    τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_magSubspace_component_lt_of_predictedGS
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hA_lowered hB_lowered τ => by
        have hcross :
            (sublatticeSpinSOpPlus N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) +
              (sublatticeSpinSOpPlus N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              bipartiteToyMinEnergyPredicted (Λ := V) A N • Ψ -
                ((2 : ℂ) •
                  (sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N (fun x => ! A x))).mulVec Ψ :=
          tasaki23_cross_ladder_raised_lowered_components_eq_energy_sub_two_op3_of_predictedGS
            (V := V) A N hΨ_pred
        exact
          hsource_lowered_joint_cross_ladder_component_lt hM hMlt hμ_lt hv_pos hΦ
            Ψ hΨ_eq hΨ_pred hcross hA_lowered hB_lowered τ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS interval chain with
unpacked lowered joint cross-ladder data**: refine the cross-ladder-aware
callback so it receives the lowered components' explicit sublattice
Casimir equations and successor-sector support, rather than the packed
`tasaki23LoweredJointMagSubspace` memberships.

This is the form needed for the remaining representation-theoretic
comparison: the callback has the cross-ladder equation, the two maximum
Casimir equations for each lowered component, and the common successor
magnetization support. -/
theorem
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_lowered_joint_cross_ladder_component_lt_of_predictedGS
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
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_lowered_joint_cross_ladder_component_lt_of_predictedGS
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hcross hA_lowered hB_lowered τ => by
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

end LatticeSystem.Quantum
