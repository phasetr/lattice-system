import LatticeSystem.Quantum.SpinS.Theorem23IntervalCasimir

/-!
# Tasaki §2.5 Theorem 2.3 interval-Casimir minimality suffix

This module contains the global / sector minimality bridges and named callback
definitions split from `Theorem23IntervalCasimir.lean`. The base
interval-Casimir module keeps the predicted-Casimir interval-chain wrappers,
while this suffix exposes the final minimality bridge and callback API consumed
by the outside-ground and final-boundary modules.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.

Tracked in Issue #412 (Tasaki §2.5: Marshall–Lieb–Mattis theorem).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 global-minimality bridge from sectors**:
to prove the full-Hilbert-space global minimality clause, it is enough to
prove the same lower bound in every magnetization sector.

Given a nonzero full-space eigenvector, choose a configuration where it is
nonzero, restrict to that configuration's `magSumS` sector, and use the
sector-restriction eigenvector bridge. This reduces the remaining global
minimality input for Theorem 2.3 to a sectorwise statement. -/
theorem tasaki23_global_minimality_of_sector_minimality
    {J : V → V → ℂ} (N : ℕ) {μ : ℝ}
    (hsector_min :
      ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
        ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
          Φ ≠ 0 →
          (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
            (μ' : ℂ) • Φ →
          μ ≤ μ') :
    ∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
      Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
      μ ≤ μ' := by
  intro μ' Ψ' hΨ'_ne hΨ'_eigen
  classical
  have hnonzero_point : ∃ σ : V → Fin (N + 1), Ψ' σ ≠ 0 := by
    by_contra h
    apply hΨ'_ne
    funext σ
    by_contra hσ
    exact h ⟨σ, hσ⟩
  obtain ⟨σ, hσ_ne⟩ := hnonzero_point
  let M : ℕ := magSumS σ
  letI : Nonempty (magConfigS V N M) := ⟨⟨σ, rfl⟩⟩
  have hrestr_ne :
      magSectorRestriction (M := M) Ψ' ≠ 0 := by
    intro hzero
    have hval := congrFun hzero ⟨σ, rfl⟩
    exact hσ_ne hval
  have hrestr_eigen :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (magSectorRestriction (M := M) Ψ') =
        (μ' : ℂ) • magSectorRestriction (M := M) Ψ' :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
      J hΨ'_eigen
  exact hsector_min M hrestr_ne hrestr_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-minimality bridge from real sectors**:
for real coupling, it is enough to prove the sector lower bound for
nonzero real-form sector eigenvectors.

An arbitrary nonzero complex sector eigenvector has either nonzero real
part or nonzero imaginary part.  Since the complex sector matrix has real
entries under `hJ_real`, that nonzero component is an eigenvector of the
real-form sector matrix at the same real eigenvalue. -/
theorem tasaki23_sector_minimality_of_real_sector_minimality
    {J : V → V → ℂ} (N : ℕ) {μ : ℝ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hreal_sector_min :
      ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
        ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
          φ ≠ 0 →
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ' • φ →
          μ ≤ μ') :
    ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
      ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
        Φ ≠ 0 →
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
          (μ' : ℂ) • Φ →
        μ ≤ μ' := by
  intro M _ μ' Φ hΦ_ne hΦ_eigen
  classical
  by_cases hRe_ne : (fun σ : magConfigS V N M => (Φ σ).re) ≠ 0
  · exact hreal_sector_min M hRe_ne
      (heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hΦ_eigen)
  · have hRe_zero : (fun σ : magConfigS V N M => (Φ σ).re) = 0 := by
      by_contra h
      exact hRe_ne h
    have hIm_ne : (fun σ : magConfigS V N M => (Φ σ).im) ≠ 0 := by
      intro hIm_zero
      apply hΦ_ne
      funext σ
      apply Complex.ext
      · have h := congrFun hRe_zero σ
        simpa using h
      · have h := congrFun hIm_zero σ
        simpa using h
    exact hreal_sector_min M hIm_ne
      (heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
        N hJ_real hΦ_eigen)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 common-energy chain callback**:
the adjacent-sector chain has produced one real energy `μ` realised by a
strictly positive Marshall representative in every admissible
`tasaki23GroundStateSectors` sector.

This names the central interval-chain output used by the final global
minimality wrappers. -/
def tasaki23CommonEnergyChain
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c μ : ℝ) : Prop :=
  ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
    ∃ v : magConfigS V N M → ℝ,
      μ < c ∧ (∀ τ, 0 < v τ) ∧
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 common-energy chain from predecessor
difference positivity**: the left-endpoint predicted-GS input together
with the fully threaded predecessor-difference callback produces the
named common-energy chain used by the outside-sector final wrapper.

This packages the existing interval-chain route and forgets the extra
predicted toy ground-state membership carried by
`tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos`. -/
theorem
    tasaki23_common_energy_chain_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
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
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c) :
    ∃ μ : ℝ, tasaki23CommonEnergyChain (V := V) A J N c μ := by
  obtain ⟨μ, hchain_pred⟩ :=
    tasaki23_energy_interval_chain_with_predictedGS_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      hpredecessor_difference
  refine ⟨μ, ?_⟩
  intro M hM
  obtain ⟨v, hμ_lt, hv_pos, hΦ, _hpredictedGS⟩ := hchain_pred M hM
  exact ⟨v, hμ_lt, hv_pos, hΦ⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 common-energy chain from uniform predicted-GS
callbacks**: the uniform source predicted-GS callback supplies the left-endpoint
predicted-GS input needed by the predecessor-difference interval chain.

This wrapper keeps the visible predicted-GS hypothesis in the canonical
source-sector form used by the adjacent-sector chain and reuses
`tasaki23_common_energy_chain_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos`
for the actual common-energy construction. -/
theorem
    tasaki23_common_energy_chain_of_source_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
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
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c) :
    ∃ μ : ℝ, tasaki23CommonEnergyChain (V := V) A J N c μ :=
  tasaki23_common_energy_chain_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
    A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate hBA hsector_nonempty
    (fun {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ} hμ_lt hv_pos hΦ =>
      hsource_predictedGS
        (M :=
          min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N)
        (by
          simpa using tasaki23GroundStateSectors_left_mem (V := V) A N)
        hμ_lt hv_pos hΦ)
    hpredecessor_difference

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 common-energy chain with discharged
admissible-sector non-emptiness**: the uniform source predicted-GS callback and
predecessor-difference callback imply the named common-energy chain, while
sector non-emptiness is supplied from the physical range of
`tasaki23GroundStateSectors`.

This is the same source predicted-GS common-energy boundary as
`tasaki23_common_energy_chain_of_source_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos`,
but with the admissible-sector `Nonempty` callback discharged by
`magConfigS_nonempty_of_le_card_mul`. -/
theorem
    tasaki23_common_energy_chain_of_source_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos_discharge_nonempty
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
    (hsource_predictedGS :
      tasaki23SourcePredictedGSCallback (V := V) A J N c)
    (hpredecessor_difference :
      tasaki23PredecessorDifferenceCallback (V := V) A J N c) :
    ∃ μ : ℝ, tasaki23CommonEnergyChain (V := V) A J N c μ :=
  tasaki23_common_energy_chain_of_source_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
    A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
    hc_strict h_intermediate hBA
    (fun _M hM =>
      magConfigS_nonempty_of_le_card_mul (V := V) (N := N)
        (tasaki23GroundStateSectors_le_card_mul (V := V) A N hM))
    hsource_predictedGS hpredecessor_difference

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 common-energy chain from predecessor
raising-source dominance**: the left-endpoint predicted-GS input together
with the fully threaded strict dominance of the on-`A` predecessor
raising-source sum by the off-`A` sum produces the named common-energy
chain used by the outside-sector final wrapper.

The theorem converts the strict dominance callback into the
predecessor-difference callback by `linarith`, then reuses
`tasaki23_common_energy_chain_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos`. -/
theorem
    tasaki23_common_energy_chain_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_raising_source_sum_lt
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
    (hpredecessor_raising_source_sum_lt :
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
              ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
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
                          τ x.1 ((Finset.mem_filter.mp x.2).2)⟩))) :
    ∃ μ : ℝ, tasaki23CommonEnergyChain (V := V) A J N c μ := by
  exact
    tasaki23_common_energy_chain_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_difference_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        have hlt :=
          hpredecessor_raising_source_sum_lt
            hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
            hB_A hB_B hB_mag τ
        linarith)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 common-energy chain from explicit
lowerable positive-source coefficients**: the left-endpoint predicted-GS
input together with the fully threaded strict dominance of the attached
explicit lowerable positive-source coefficient sums produces the named
common-energy chain used by the outside-sector final wrapper.

The theorem converts the explicit lowerable coefficient dominance into
the predecessor raising-source dominance by the coefficient mirror
`tasaki23_raising_predecessor_source_sum_lt_of_lowerable_positive_source_attach_sum_lt`,
then reuses
`tasaki23_common_energy_chain_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_raising_source_sum_lt`. -/
theorem
    tasaki23_common_energy_chain_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_explicit_lowerable_positive_source_coefficient_lt
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
    (hpredecessor_explicit_lowerable_positive_source_coefficient_lt :
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
              ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
              ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x => (! A x) = true)).card : ℂ) *
                  ((N : ℂ) / 2)) + 1)) •
                ((sublatticeSpinSOpMinus N A).mulVec Ψ) →
            ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
              magSubspaceS V N
                (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) →
            (sublatticeSpinSquaredS N A).mulVec
                ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) =
              ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
                  ((N : ℂ) / 2)) *
                ((((Finset.univ.filter (fun x => A x = true)).card : ℂ) *
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
              (((Finset.univ.filter (fun x : V => A x = true)).filter
                    (fun x : V => 0 < (τ.1 x).val)).attach.sum
                  (fun x =>
                    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                      v τ x.1 ((Finset.mem_filter.mp x.2).2))) <
                (((Finset.univ.filter (fun x : V => A x = false)).filter
                    (fun x : V => 0 < (τ.1 x).val)).attach.sum
                  (fun x =>
                    tasaki23LoweringPredecessorPositiveSourceLowerableCoefficient
                      v τ x.1 ((Finset.mem_filter.mp x.2).2)))) :
    ∃ μ : ℝ, tasaki23CommonEnergyChain (V := V) A J N c μ := by
  exact
    tasaki23_common_energy_chain_of_left_endpoint_predictedGS_of_unpacked_reembedded_real_source_weight_predecessor_raising_source_sum_lt
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hleft_predictedGS
      (by
        intro M hM hMlt μ v hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B
          hA_mag hB_A hB_B hB_mag τ
        exact
          tasaki23_raising_predecessor_source_sum_lt_of_lowerable_positive_source_attach_sum_lt
            (V := V) (N := N) A v τ
            (hpredecessor_explicit_lowerable_positive_source_coefficient_lt
              hM hMlt hμ_lt hv_pos hΦ Ψ hΨ_eq hΨ_pred hpred hA_A hA_B hA_mag
              hB_A hB_B hB_mag τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-minimality callback**:
after the common-energy chain has selected `μ`, this callback states that
`μ` is a lower bound for every nonzero complex eigenvector in every
magnetization sector.

This names the sectorwise global-minimality input used by the direct
lowered-site-sum final wrappers. -/
def tasaki23SectorMinimalityCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ {μ : ℝ},
    tasaki23CommonEnergyChain (V := V) A J N c μ →
      ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
        ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
          Φ ≠ 0 →
          (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
            (μ' : ℂ) • Φ →
          μ ≤ μ'


end LatticeSystem.Quantum
