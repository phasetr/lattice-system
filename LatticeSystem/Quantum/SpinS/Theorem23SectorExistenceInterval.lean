import LatticeSystem.Quantum.SpinS.Theorem23SectorExistence

/-!
# Tasaki §2.5 Theorem 2.3 sector-existence interval API

This module contains the predicted-GS energy interval-chain wrappers split
from `Theorem23SectorExistence.lean`. Keeping this suffix separate lets the
base sector-existence module elaborate without replaying the interval-induction
wrappers.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS energy interval chain**:
in the canonical orientation `|¬A| ≤ |A|`, choose the left endpoint
sector by the per-sector Theorem 2.2 wrapper and propagate its energy
through the whole admissible interval by the predicted-GS lowered
dominance common-energy step.

The theorem deliberately keeps the two remaining mathematical inputs as
callbacks for each currently chosen source vector: membership in
`bipartiteToyGroundStateSubspacePredicted A N` and the lowered off-`A`
dominance estimate. It isolates the discrete interval induction needed
for the final Theorem 2.3 proof. -/
theorem tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_onA_neg_lt_offA
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
    (hsource_pred :
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
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
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
          tasaki23_successor_sector_common_energy_of_onA_neg_lt_offA_of_mem_bipartiteToyGroundStateSubspacePredicted
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hBA hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ
            (hsource_pred hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
            (hsource_dominance hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS energy interval chain from
lowered site-sum positivity**: in the canonical orientation `|¬A| ≤ |A|`,
choose the left endpoint sector by the per-sector Theorem 2.2 wrapper and
propagate its energy through the whole admissible interval using the
direct lowered site-sum positivity successor step.

Compared with
`tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_onA_neg_lt_offA`,
this version keeps the actual Marshall-positivity input for
`S^-_{\mathrm{tot}}` as a strict site-sum positivity callback, without
packaging it first as an off-`A`/on-`A` dominance inequality. -/
theorem tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
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
    (hsource_pred :
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
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
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
          tasaki23_successor_sector_common_energy_of_site_sum_pos_of_mem_bipartiteToyGroundStateSubspacePredicted
            A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
            hc_strict h_intermediate hBA hM_mem (by simpa [right] using hMlt)
            hμ_lt hv_pos hΦ
            (hsource_pred hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
            (hsource_site_sum_pos hM_mem (by simpa [right] using hMlt) hμ_lt hv_pos hΦ)
        rcases hstep with ⟨_hsucc_mem, _hμ_lt, _hv_pos, _hΦ, _hne,
          v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, _hr⟩
        exact ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ⟩
  intro M hM
  have hbounds := (tasaki23GroundStateSectors_mem_iff (V := V) A N M).mp hM
  exact hchain M (by simpa [left] using hbounds.1) (by simpa [right] using hbounds.2)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS energy interval chain from
lowered vector Marshall positivity**: in the canonical orientation
`|¬A| ≤ |A|`, choose the left endpoint sector by the per-sector
Theorem 2.2 wrapper and propagate its energy through the admissible
interval using the actual Marshall positivity of the lowered ladder
image.

This is the vector-positivity version of
`tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_site_sum_pos`.
The source-form bridge
`tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos` converts
the Marshall-signed positive real representative input into the site-sum
callback consumed by the existing successor step. -/
theorem tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_marshall_pos
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
    (hsource_pred :
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
          magSectorEmbedding
              (fun τ : magConfigS V N M =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
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
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
  exact
    tasaki23_energy_interval_chain_of_left_endpoint_predictedGS_of_lowered_site_sum_pos
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hBA hsector_nonempty hsource_pred
      (fun {M : ℕ} hM hMlt {μ : ℝ} {v : magConfigS V N M → ℝ}
          hμ_lt hv_pos hΦ =>
        tasaki23_lowered_site_sum_pos_of_source_lowered_marshall_pos A v
          (hsource_lowered_marshall_pos hM hMlt hμ_lt hv_pos hΦ))


end LatticeSystem.Quantum
