import LatticeSystem.Quantum.SpinS.Theorem23Interval

/-!
# Tasaki §2.5 Theorem 2.3 interval Casimir API

This module contains the predicted-Casimir interval-chain wrappers and
the sector-minimality callbacks split from `Theorem23Interval.lean`.
Keeping this suffix separate lets the base interval-chain callback API
elaborate without replaying the predicted-Casimir and final minimality
bridges.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-Casimir energy interval chain**:
in the canonical orientation `|¬A| ≤ |A|`, choose the left endpoint sector
by the per-sector Theorem 2.2 wrapper and propagate its energy through the
whole admissible interval using the lowered dominance successor step.

Compared with
`tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_onA_neg_lt_offA`,
this version asks directly for the source vector's predicted total-Casimir
identity instead of membership in the predicted toy ground-state subspace. -/
theorem tasaki23_energy_interval_chain_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA
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
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hsource_casimir :
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
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
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
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ⟩ := ih hM_le_right
        have hstep :=
          tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_predictedCasimirValue
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ
            (hsource_casimir hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
            (hsource_dominance hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 threaded predicted-Casimir interval chain**:
choose the left endpoint sector by the per-sector Theorem 2.2 wrapper and
propagate both the common energy and the predicted total-Casimir identity
through the whole admissible interval.

Compared with
`tasaki23_energy_interval_chain_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA`,
this version only asks for the predicted-Casimir identity at the left endpoint.
The induction invariant carries the successor Casimir returned by the adjacent
common-energy step. -/
theorem
    tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA
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
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_casimir :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
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
          ∀ τ : magConfigS V N (M + 1),
            -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
              ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
                tasaki23SignedLoweringSiteContribution A
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hcas_left :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N left =>
              (((marshallSignS A τ.1).re * v_left τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N left =>
              (((marshallSignS A τ.1).re * v_left τ : ℝ) : ℂ)) := by
    simpa [left] using hleft_casimir hμ_left_lt hv_left_pos hΦ_left
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left, hcas_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ, hcas⟩ := ih hM_le_right
        have hstep :=
          tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_onA_neg_lt_offA
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ hcas
            (hsource_dominance hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 threaded predicted-Casimir interval chain
from lowered site-sum positivity**: choose the left endpoint sector by the
per-sector Theorem 2.2 wrapper and propagate both the common energy and the
predicted total-Casimir identity through the whole admissible interval.

Compared with
`tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_onA_neg_lt_offA`,
this version uses the direct lowered site-sum positivity callback instead of
the off-`A`/on-`A` dominance formulation. -/
theorem
    tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_lowered_site_sum_pos
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
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_casimir :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_site_sum_pos :
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
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (∑ x : V,
                (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
                  (magSectorEmbedding
                    (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  let left : ℕ :=
    min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  let right : ℕ :=
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
      (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N
  have hleft_mem : left ∈ tasaki23GroundStateSectors (V := V) A N := by
    simpa [left] using tasaki23GroundStateSectors_left_mem (V := V) A N
  letI : Nonempty (magConfigS V N left) := hsector_nonempty left hleft_mem
  obtain ⟨μ, v_left, hμ_left_lt, hv_left_pos, hΦ_left, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := left) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hcas_left :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N left =>
              (((marshallSignS A τ.1).re * v_left τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N left =>
              (((marshallSignS A τ.1).re * v_left τ : ℝ) : ℂ)) := by
    simpa [left] using hleft_casimir hμ_left_lt hv_left_pos hΦ_left
  refine ⟨μ, ?_⟩
  have hchain :
      ∀ M, left ≤ M → M ≤ right →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
    intro M hleft_le hright_le
    induction M, hleft_le using Nat.le_induction with
    | base =>
        exact ⟨v_left, hμ_left_lt, hv_left_pos, hΦ_left, hcas_left⟩
    | succ M hleft_le ih =>
        have hM_le_right : M ≤ right := Nat.le_of_succ_le hright_le
        have hMlt : M < right := Nat.lt_of_succ_le hright_le
        have hM_mem : M ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          simpa [left, right] using And.intro hleft_le hM_le_right
        have hsucc_mem : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N := by
          rw [tasaki23GroundStateSectors_mem_iff]
          have hleft_succ : left ≤ M + 1 := hleft_le.trans (Nat.le_succ M)
          simpa [left, right] using And.intro hleft_succ hright_le
        letI : Nonempty (magConfigS V N M) :=
          hsector_nonempty M hM_mem
        letI : Nonempty (magConfigS V N (M + 1)) :=
          hsector_nonempty (M + 1) hsucc_mem
        obtain ⟨v, hμ_lt, hv_pos, hΦ, hcas⟩ := ih hM_le_right
        have hstep :=
          tasaki23_successor_sector_common_energy_with_successor_predictedCasimir_of_site_sum_pos
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ hcas
            (hsource_site_sum_pos hM_mem (by simpa [right] using hMlt)
              hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 threaded predicted-Casimir interval chain
from lowered vector Marshall positivity**: this is the vector-positivity
version of
`tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_lowered_site_sum_pos`.
The source-form bridge
`tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos` converts
the lowered ladder-vector positivity hypothesis for the Marshall-signed
positive real representative into the site-sum callback. -/
theorem
    tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_lowered_marshall_pos
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
    (hsector_nonempty :
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        Nonempty (magConfigS V N M))
    (hleft_casimir :
      ∀ {μ : ℝ}
        {v : magConfigS V N
          (min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
            (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
              N) → ℝ},
          μ < c →
          (∀ τ, 0 < v τ) →
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_lowered_marshall_pos :
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
          ∀ τ : magConfigS V N (M + 1),
            0 < (marshallSignS A τ.1).re *
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re) :
    ∃ μ : ℝ,
      ∀ M, M ∈ tasaki23GroundStateSectors (V := V) A N →
        ∃ v : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v τ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  exact
    tasaki23_energy_interval_chain_with_predictedCasimir_of_left_endpoint_predictedCasimir_of_lowered_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hsector_nonempty hleft_casimir
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ =>
        tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos A v
          (hsource_lowered_marshall_pos hM hMlt hμ_lt hv_pos hΦ))

set_option linter.style.longLine false in
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
