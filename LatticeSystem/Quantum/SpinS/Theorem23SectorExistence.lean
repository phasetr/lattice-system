import LatticeSystem.Quantum.SpinS.Theorem23Dominance
import LatticeSystem.Quantum.SpinS.Theorem23LocalCoefficient
import LatticeSystem.Quantum.SpinS.Theorem23LocalDifferenceMarshall

/-!
# Tasaki §2.5 Theorem 2.3 sector-existence API

This module contains the final `tasaki_2_5_theorem_2_3` statement,
the per-sector Theorem 2.2 reuse wrapper, and the sector-existence
interval-chain wrappers split from `Theorem23.lean`. Keeping this layer
separate lets the adjacent common-energy and dominance APIs elaborate without
the sector-existence/final-statement tail.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 (Marshall–Lieb–Mattis general spin-S), final
statement** as a `Prop`.

The hypothesis bundle matches the per-sector bundled Theorem 2.2
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full`
(PR #869) exactly. Given:
- real symmetric coupling `J` (`(J x y).im = 0`, `star (J x y) = J x y`,
  `J x y = J y x`, `0 ≤ (J x y).re`);
- bipartite support (`A x = A y → J x y = 0`);
- positive on the bipartite complete graph (`Adj → 0 < (J x y).re`);
- non-empty sublattices (`|A| ≥ 1`, `|¬A| ≥ 1`);
- a uniform spectral shift `c` strictly above the dressed diagonal;
- the intermediate-existence hypothesis from Theorem 2.2 (#869);
- each admissible sector `M` is non-empty;

the conclusion asserts existence of a common ground-state energy `μ`
realised on every admissible sector by a Marshall-positive
eigenvector (Tasaki (2.5.4) with `σ = M`), with within-sector
uniqueness up to positive scalar, plus global minimality of `μ`.

The proof iterates #869 sector-by-sector across
`tasaki23GroundStateSectors A N`. -/
def tasaki_2_5_theorem_2_3
    (A : V → Bool) (N : ℕ) (J : V → V → ℂ) (c : ℝ) : Prop :=
  -- Coupling hypotheses (matching #869's bundle).
  (∀ x y, (J x y).im = 0) →
  (∀ x y, star (J x y) = J x y) →
  (∀ x y, J x y = J y x) →
  (∀ x y, 0 ≤ (J x y).re) →
  (∀ x y, A x = A y → J x y = 0) →
  (∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re) →
  -- Spectral shift strictly above the dressed diagonal (matching #869).
  (∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c) →
  -- Intermediate-existence hypothesis (matching #869).
  (∀ τ : V → Fin (N + 1), ∀ x : V, ∃ z, A z ≠ A x ∧ (τ z).val < N) →
  -- Non-empty sublattices (Tasaki Theorem 2.3 hypothesis `|A| ≥ 1`, `|¬A| ≥ 1`).
  (1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card) →
  (1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card) →
  -- Conclusion.
  ∃ μ : ℝ,
    -- (Existence + Marshall expansion + sector uniqueness) per admissible sector.
    (∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      [Nonempty (magConfigS V N M)] →
      ∃ v : magConfigS V N M → ℝ,
        μ < c ∧ (∀ σ, 0 < v σ) ∧
        (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
          (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
          (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
          (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
          μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ))) ∧
    -- Global minimality of μ across all eigenvalues.
    (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
      Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
      μ ≤ μ')

/-- **Per-sector existence step (toward Tasaki §2.5 Theorem 2.3 proof)**.

For each admissible magnetization sector `M ∈ tasaki23GroundStateSectors A N`
with `Nonempty (magConfigS V N M)`, the per-sector bundled Theorem 2.2
`marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full` (#869)
gives a Marshall-positive ground state of the spin-`S` antiferromagnetic
Heisenberg Hamiltonian (Tasaki (2.5.4) with `σ = M`) at some sector
eigenvalue `μ_M < c`, plus within-sector uniqueness up to positive scalar.

This is the first step of the Tasaki §2.5 Theorem 2.3 proof
("essentially a straightforward modification of that of Theorem 2.2"):
the proof of `tasaki_2_5_theorem_2_3` then iterates this per-sector
existence across the admissible range and shows the sector eigenvalues
`μ_M` coincide (constancy via the SU(2) ladder
`heisenbergHamiltonianS_commute_totalSpinSOpMinus`) and that the common
value is the global minimum.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42. -/
theorem tasaki_2_5_theorem_2_3_sector_existence
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
      (∀ σ, magSumS σ ≠ M →
        magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) σ = 0) ∧
      (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
        (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
        μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N M,
            (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ)) :=
  marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full
    A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate

/-- **Tasaki §2.5 Theorem 2.3 sector-existence successor chain link
with predicted Casimir**: choose the source-sector Marshall-positive
ground-state vector from the per-sector Theorem 2.2 wrapper, then apply
the adjacent ladder-image predicted-Casimir successor package.

The remaining hypotheses are exactly the two mathematical inputs still
needed for the chosen Theorem 2.2 sector vector: predicted total-Casimir
eigenvalue and lowered site-sum positivity. -/
theorem tasaki23_successor_sector_existence_with_lowered_predictedCasimir
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_cas :
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
    (hsource_site_sum :
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
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  obtain ⟨μ, v, hμ_lt, hv_pos, hΦ, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  exact ⟨μ, v,
    tasaki23_successor_common_energy_with_lowered_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (hsource_cas hμ_lt hv_pos hΦ)
      (hsource_site_sum hμ_lt hv_pos hΦ)⟩

/-- **Tasaki §2.5 Theorem 2.3 successor predicted-Casimir
propagation**: in the lowering-direction sector-existence step, the
successor representative returned by the adjacent-sector comparison also
has the Theorem 2.3 predicted total-Casimir eigenvalue.

The existing package already proves that the lowered source vector has
the predicted Casimir eigenvalue and that its real parts are a positive
real scalar multiple of the successor representative in Marshall
coordinates.  Since both vectors are real and supported in the successor
sector, this is a full scalar equality, so the Casimir eigenvector
equation cancels the scalar. -/
theorem
    tasaki23_successor_sector_existence_with_successor_predictedCasimir
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_cas :
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
    (hsource_site_sum :
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
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
              magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  obtain ⟨μ, v, hpack⟩ :=
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hsource_cas hsource_site_sum
  have hM_succ := hpack.1.1
  have hμ_lt := hpack.1.2.1
  have hv_pos := hpack.1.2.2.1
  have hΦ := hpack.1.2.2.2.1
  have hlowered_ne := hpack.1.2.2.2.2.1
  have hsucc := hpack.1.2.2.2.2.2
  have hcas_lowered := hpack.2
  obtain ⟨v_succ, hsucc_pack⟩ := hsucc
  have hμ_succ_lt := hsucc_pack.1
  have hv_succ_pos := hsucc_pack.2.1
  have hΦ_succ := hsucc_pack.2.2.1
  obtain ⟨r, hr_pos, hrel⟩ := hsucc_pack.2.2.2
  have hsmul :
      (totalSpinSOpMinus V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (r : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    totalSpinSOpMinus_marshallSignedEmbedding_eq_smul_successor_of_re
      A hrel
  have hsucc_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
          magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) :=
    tasaki23_totalSpinSSquared_predictedCasimirValue_of_real_smul_eq
      A N (ne_of_gt hr_pos) hsmul hcas_lowered
  exact ⟨μ, v,
    ⟨hM_succ, hμ_lt, hv_pos, hΦ, hlowered_ne,
      ⟨v_succ, hμ_succ_lt, hv_succ_pos, hΦ_succ, hsucc_cas,
        ⟨r, hr_pos, hrel⟩⟩⟩,
    hcas_lowered⟩

/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted Casimir**: choose the sector-`M+1` Marshall-positive
ground-state vector from the per-sector Theorem 2.2 wrapper, then apply
the adjacent ladder-image predicted-Casimir predecessor package.

This is the raising-direction companion to
`tasaki23_successor_sector_existence_with_lowered_predictedCasimir`. -/
theorem tasaki23_predecessor_sector_existence_with_raised_predictedCasimir
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_site_sum :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          0 < (marshallSignS A τ.1).re *
            (∑ x : V,
              (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re)) :
    ∃ (μ : ℝ) (v : magConfigS V N (M + 1) → ℝ),
      (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_pred : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (((totalSpinSOpPlus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  obtain ⟨μ, v, hμ_lt, hv_pos, hΦ, _hsupport, _huniq⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M + 1) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict h_intermediate
  exact ⟨μ, v,
    tasaki23_predecessor_common_energy_with_raised_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hμ_lt hv_pos hΦ
      (hsource_cas hμ_lt hv_pos hΦ)
      (hsource_site_sum hμ_lt hv_pos hΦ)⟩

/-- **Tasaki §2.5 Theorem 2.3 sector-existence successor chain link
with predicted Casimir from lowered dominance**: choose the source-sector
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, convert the lowered off-`A` dominance hypothesis into strict
lowered site-sum positivity, then apply the predicted-Casimir successor
package.

The dominance estimate remains an explicit hypothesis; this theorem only
connects that estimate to the sector-existence adjacent-chain wrapper. -/
theorem
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_cas :
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
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hsource_cas
      (fun {μ : ℝ} {v : magConfigS V N M → ℝ} hμ_lt hv_pos hΦ τ =>
        tasaki23_signed_lowering_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hsource_dominance hμ_lt hv_pos hΦ τ))

/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted Casimir from raised dominance**: choose the sector-`M+1`
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, convert the raised off-`A` dominance hypothesis into strict
raised site-sum positivity, then apply the predicted-Casimir predecessor
package.

This is the raising-direction companion to the lowered dominance wrapper
above. -/
theorem
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    (hsource_cas :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            magSectorEmbedding
              (fun τ : magConfigS V N (M + 1) =>
                (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N (M + 1) → ℝ),
      (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_pred : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (((totalSpinSOpPlus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt hsource_cas
      (fun {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ} hμ_lt hv_pos hΦ τ =>
        tasaki23_signed_raising_site_sum_pos_of_onA_neg_lt_offA
          A (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
          τ (hsource_dominance hμ_lt hv_pos hΦ τ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-existence successor chain link
with predicted-GS membership from lowered dominance**: in the canonical
orientation `|¬A| ≤ |A|`, choose the source-sector Marshall-positive
ground-state vector from the per-sector Theorem 2.2 wrapper, use
predicted-GS membership to supply the predicted-Casimir input, and
convert the lowered off-`A` dominance hypothesis into the strict
site-sum positivity input.

The membership and dominance estimates remain explicit callbacks for the
chosen source-sector vector. -/
theorem
    tasaki23_successor_sector_existence_with_lowered_predictedGS_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
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
    (hM : M ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt : M <
      max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N)
    (hsource_pred :
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
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      (M + 1 ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_succ : magConfigS V N (M + 1) → ℝ,
          μ < c ∧ (∀ τ, 0 < v_succ τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N (M + 1),
              (((totalSpinSOpMinus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_succ τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpMinus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N M =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_successor_sector_existence_with_lowered_predictedCasimir_of_onA_neg_lt_offA
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt
      (fun {μ : ℝ} {v : magConfigS V N M → ℝ} hμ_lt hv_pos hΦ =>
        tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
          A N hBA (hsource_pred hμ_lt hv_pos hΦ))
      hsource_dominance

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector-existence predecessor chain link
with predicted-GS membership from raised dominance**: in the canonical
orientation `|¬A| ≤ |A|`, choose the sector-`M+1`
Marshall-positive ground-state vector from the per-sector Theorem 2.2
wrapper, use predicted-GS membership to supply the predicted-Casimir
input, and convert the raised off-`A` dominance hypothesis into the
strict site-sum positivity input.

This is the raising-direction companion to the lowered predicted-GS
sector-existence wrapper. -/
theorem
    tasaki23_predecessor_sector_existence_with_raised_predictedGS_of_onA_neg_lt_offA
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)] [Nonempty (magConfigS V N (M + 1))]
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
    (hM : M + 1 ∈ tasaki23GroundStateSectors (V := V) A N)
    (hMlt :
      min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) * N <
          M + 1)
    (hsource_pred :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
          bipartiteToyGroundStateSubspacePredicted (Λ := V) A N)
    (hsource_dominance :
      ∀ {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ},
        μ < c →
        (∀ τ, 0 < v τ) →
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
        ∀ τ : magConfigS V N M,
          -(∑ x ∈ (Finset.univ.filter (fun x : V => A x = true)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) <
            ∑ x ∈ (Finset.univ.filter (fun x : V => A x = false)),
              tasaki23SignedRaisingSiteContribution A
                (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) τ x) :
    ∃ (μ : ℝ) (v : magConfigS V N (M + 1) → ℝ),
      (M ∈ tasaki23GroundStateSectors (V := V) A N ∧
        μ < c ∧ (∀ τ, 0 < v τ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
        ∃ v_pred : magConfigS V N M → ℝ,
          μ < c ∧ (∀ τ, 0 < v_pred τ) ∧
          (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
          ∃ r : ℝ, 0 < r ∧
            ∀ τ : magConfigS V N M,
              (((totalSpinSOpPlus V N).mulVec
                (magSectorEmbedding
                  (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
                r * ((marshallSignS A τ.1).re * v_pred τ)) ∧
        (totalSpinSSquared V N).mulVec
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) =
          (tasaki23PredictedCasimirValue (V := V) A N : ℂ) •
            ((totalSpinSOpPlus V N).mulVec
              (magSectorEmbedding
                (fun τ : magConfigS V N (M + 1) =>
                  (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) := by
  exact
    tasaki23_predecessor_sector_existence_with_raised_predictedCasimir_of_onA_neg_lt_offA
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate hM hMlt
      (fun {μ : ℝ} {v : magConfigS V N (M + 1) → ℝ} hμ_lt hv_pos hΦ =>
        tasaki23_totalSpinSSquared_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
          A N hBA (hsource_pred hμ_lt hv_pos hΦ))
      hsource_dominance

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
