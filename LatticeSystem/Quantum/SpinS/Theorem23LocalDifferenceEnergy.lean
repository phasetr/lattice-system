import LatticeSystem.Quantum.SpinS.Theorem23LocalDifference

/-!
# Tasaki §2.5 Theorem 2.3 local-difference energy API

This module contains the adjacent-sector energy comparison packages
split from `Theorem23LocalDifference.lean`. Keeping this suffix in
its own module lets the local predecessor-difference, site-sum, and
Marshall-positivity bridges elaborate separately from the energy
identification wrappers.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector energy step, lowering
direction**: if a source-sector eigenvector is embedded from
`magSumS = M`, and its lowered vector `Ŝ^-_tot Ψ` is Marshall-positive
in the adjacent sector `M + 1`, then the target sector's Theorem 2.2
ground-state eigenvalue is the same eigenvalue.

This isolates the exact remaining positivity input in the proof of
Tasaki §2.5 Theorem 2.3: after ladder eigenvalue preservation and the
sector-support shift, the target-sector uniqueness clause identifies
the neighboring sector energy. -/
theorem tasaki23_lowering_identifies_adjacent_sector_energy
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N M → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hlowered_marshall_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re) :
    ∃ (μ_succ : ℝ) (v_succ : magConfigS V N (M + 1) → ℝ),
      μ_succ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ_succ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      μ = μ_succ ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  obtain ⟨μ_succ, v_succ, hμ_succ_lt, hv_succ_pos, hmul_succ,
      _hsupp_succ, huniq_succ⟩ :=
    marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full
      (M := M + 1) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hlowered_eigen :
      (heisenbergHamiltonianS J N).mulVec
        ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) =
        (μ : ℂ) • ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) :=
    heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_of_eigenvec J N hΦ
  have hlowered_supp :
      ∀ σ : V → Fin (N + 1), magSumS σ ≠ M + 1 →
        ((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) σ = 0 :=
    totalSpinSOpMinus_mulVec_magSectorEmbedding_supported_succ Φ
  obtain ⟨hμ_eq, r, hr_pos, hrel⟩ :=
    huniq_succ hlowered_eigen hlowered_supp hlowered_marshall_pos
  exact ⟨μ_succ, v_succ, hμ_succ_lt, hv_succ_pos, hmul_succ, hμ_eq,
    r, hr_pos, hrel⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector energy step, raising
direction**: if a source-sector eigenvector is embedded from
`magSumS = M + 1`, and its raised vector `Ŝ^+_tot Ψ` is
Marshall-positive in the adjacent sector `M`, then the target sector's
Theorem 2.2 ground-state eigenvalue is the same eigenvalue.

This is the raising-direction companion to
`tasaki23_lowering_identifies_adjacent_sector_energy`, using the
sector-support shift for `Ŝ^+_tot`. -/
theorem tasaki23_raising_identifies_adjacent_sector_energy
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
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N (M + 1) → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hraised_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re) :
    ∃ (μ_pred : ℝ) (v_pred : magConfigS V N M → ℝ),
      μ_pred < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ_pred : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      μ = μ_pred ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  obtain ⟨μ_pred, v_pred, hμ_pred_lt, hv_pred_pos, hmul_pred,
      _hsupp_pred, huniq_pred⟩ :=
    marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full
      (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hraised_eigen :
      (heisenbergHamiltonianS J N).mulVec
        ((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) =
        (μ : ℂ) • ((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) :=
    heisenbergHamiltonianS_mulVec_totalSpinSOpPlus_of_eigenvec J N hΦ
  have hraised_supp :
      ∀ σ : V → Fin (N + 1), magSumS σ ≠ M →
        ((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) σ = 0 :=
    totalSpinSOpPlus_mulVec_magSectorEmbedding_supported_pred Φ
  obtain ⟨hμ_eq, r, hr_pos, hrel⟩ :=
    huniq_pred hraised_eigen hraised_supp hraised_marshall_pos
  exact ⟨μ_pred, v_pred, hμ_pred_lt, hv_pred_pos, hmul_pred, hμ_eq,
    r, hr_pos, hrel⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package with
non-vanishing**: the strict Marshall-positive lowered vector is
non-zero, and the adjacent target sector has the same Theorem 2.2
ground-state eigenvalue as the source sector.

This is the same conditional comparison as
`tasaki23_lowering_identifies_adjacent_sector_energy`, with the
non-zero lowered-vector conclusion made explicit for the sector-linking
proof of Theorem 2.3. -/
theorem tasaki23_lowering_identifies_adjacent_sector_energy_with_nonzero
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N M → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hlowered_marshall_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re) :
    (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
    ∃ (μ_succ : ℝ) (v_succ : magConfigS V N (M + 1) → ℝ),
      μ_succ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ_succ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      μ = μ_succ ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact ⟨tasaki23_lowered_ne_zero_of_marshall_pos A Φ hlowered_marshall_pos,
    tasaki23_lowering_identifies_adjacent_sector_energy A N c hJ_real hJ_real'
      hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate hΦ
      hlowered_marshall_pos⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package with
non-vanishing, raising direction**: the strict Marshall-positive raised
vector is non-zero, and the adjacent predecessor sector has the same
Theorem 2.2 ground-state eigenvalue as the source sector.

This is the raising-direction companion to
`tasaki23_lowering_identifies_adjacent_sector_energy_with_nonzero`. -/
theorem tasaki23_raising_identifies_adjacent_sector_energy_with_nonzero
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
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N (M + 1) → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hraised_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re) :
    (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
    ∃ (μ_pred : ℝ) (v_pred : magConfigS V N M → ℝ),
      μ_pred < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ_pred : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      μ = μ_pred ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact ⟨tasaki23_raised_ne_zero_of_marshall_pos A Φ hraised_marshall_pos,
    tasaki23_raising_identifies_adjacent_sector_energy A N c hJ_real hJ_real'
      hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate hΦ
      hraised_marshall_pos⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package with Casimir
non-vanishing, lowering direction**: for a Marshall-positive source
sector vector, a non-endpoint total-Casimir eigenvalue gives the
non-zero lowered-vector conclusion, while the existing
Marshall-positive lowered-vector hypothesis identifies the adjacent
sector energy.

This connects the Casimir obstruction package to the adjacent-sector
energy comparison used in the Theorem 2.3 chain. -/
theorem tasaki23_lowering_identifies_adjacent_sector_energy_with_casimir_nonzero
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
    {μ : ℝ} {γ : ℂ} {v : magConfigS V N M → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun τ : magConfigS V N M => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hγ_ne :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1)))
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hlowered_marshall_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re) :
    (totalSpinSOpMinus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ (μ_succ : ℝ) (v_succ : magConfigS V N (M + 1) → ℝ),
      μ_succ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ_succ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      μ = μ_succ ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    ⟨tasaki23_totalSpinSOpMinus_mulVec_marshallPositive_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
        A hΦ_cas hγ_ne hv_pos,
      tasaki23_lowering_identifies_adjacent_sector_energy A N c hJ_real
        hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
        h_intermediate hΦ hlowered_marshall_pos⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package with Casimir
non-vanishing, raising direction**: for a Marshall-positive source
sector vector, a non-endpoint total-Casimir eigenvalue gives the
non-zero raised-vector conclusion, while the existing
Marshall-positive raised-vector hypothesis identifies the adjacent
predecessor-sector energy.

This is the raising-direction companion to
`tasaki23_lowering_identifies_adjacent_sector_energy_with_casimir_nonzero`. -/
theorem tasaki23_raising_identifies_adjacent_sector_energy_with_casimir_nonzero
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
    {μ : ℝ} {γ : ℂ} {v : magConfigS V N (M + 1) → ℝ}
    (hΦ_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun τ : magConfigS V N (M + 1) =>
              (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        γ • magSectorEmbedding
          (fun τ : magConfigS V N (M + 1) =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hγ_ne :
      γ ≠
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) *
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) + 1)))
    (hv_pos : ∀ τ, 0 < v τ)
    (hΦ : (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
      (μ : ℂ) • magSectorEmbedding
        (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))
    (hraised_marshall_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re) :
    (totalSpinSOpPlus V N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ≠ 0 ∧
    ∃ (μ_pred : ℝ) (v_pred : magConfigS V N M → ℝ),
      μ_pred < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ_pred : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      μ = μ_pred ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec
            (magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)))) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact
    ⟨tasaki23_totalSpinSOpPlus_mulVec_marshallPositive_magSectorEmbedding_ne_zero_of_casimir_ne_kernel_value
        A hΦ_cas hγ_ne hv_pos,
      tasaki23_raising_identifies_adjacent_sector_energy A N c hJ_real
        hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
        h_intermediate hΦ hraised_marshall_pos⟩

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package from site-sum
positivity**: a site-sum Marshall-positivity proof for the lowered
vector is enough to obtain both non-vanishing and the adjacent-sector
ground-state energy identification.

This is the same sector-linking package as
`tasaki23_lowering_identifies_adjacent_sector_energy_with_nonzero`, but
with the remaining positivity obligation stated in the local single-site
sum form. -/
theorem tasaki23_lowering_identifies_adjacent_sector_energy_of_site_sum_pos
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N (M + 1))]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N M → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hlowered_site_sum_pos :
      ∀ τ : magConfigS V N (M + 1),
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding Φ)) τ.1).re)) :
    (totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
    ∃ (μ_succ : ℝ) (v_succ : magConfigS V N (M + 1) → ℝ),
      μ_succ < c ∧ (∀ τ, 0 < v_succ τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ))) =
        (μ_succ : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_succ τ : ℝ) : ℂ)) ∧
      μ = μ_succ ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N (M + 1),
          (((totalSpinSOpMinus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_succ τ) := by
  exact
    tasaki23_lowering_identifies_adjacent_sector_energy_with_nonzero A N c
      hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate hΦ
      (tasaki23_lowered_marshall_pos_of_site_sum_pos A Φ hlowered_site_sum_pos)

/-- **Tasaki §2.5 Theorem 2.3 adjacent-sector package from site-sum
positivity, raising direction**: a site-sum Marshall-positivity proof
for the raised vector is enough to obtain both non-vanishing and the
adjacent predecessor-sector ground-state energy identification.

This is the raising-direction companion to
`tasaki23_lowering_identifies_adjacent_sector_energy_of_site_sum_pos`. -/
theorem tasaki23_raising_identifies_adjacent_sector_energy_of_site_sum_pos
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
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {Φ : magConfigS V N (M + 1) → ℂ}
    (hΦ : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • magSectorEmbedding Φ)
    (hraised_site_sum_pos :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (∑ x : V,
            (((onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
              (magSectorEmbedding Φ)) τ.1).re)) :
    (totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ) ≠ 0 ∧
    ∃ (μ_pred : ℝ) (v_pred : magConfigS V N M → ℝ),
      μ_pred < c ∧ (∀ τ, 0 < v_pred τ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ))) =
        (μ_pred : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v_pred τ : ℝ) : ℂ)) ∧
      μ = μ_pred ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ τ : magConfigS V N M,
          (((totalSpinSOpPlus V N).mulVec (magSectorEmbedding Φ)) τ.1).re =
            r * ((marshallSignS A τ.1).re * v_pred τ) := by
  exact
    tasaki23_raising_identifies_adjacent_sector_energy_with_nonzero A N c
      hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate hΦ
      (tasaki23_raised_marshall_pos_of_site_sum_pos A Φ hraised_site_sum_pos)


end Quantum
end LatticeSystem
