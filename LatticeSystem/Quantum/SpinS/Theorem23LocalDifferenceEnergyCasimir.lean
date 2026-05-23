import LatticeSystem.Quantum.SpinS.Theorem23LocalDifferenceEnergy

/-!
# Tasaki §2.5 Theorem 2.3 adjacent-sector energy: Casimir / site-sum packages

This module contains the Casimir-non-vanishing and site-sum-positivity
adjacent-sector energy-step packages (lowering and raising directions), split
as a stable suffix from `Theorem23LocalDifferenceEnergy.lean`. The parent
module keeps the base adjacent-sector energy step and the with-nonzero
package; this module layers the Casimir-non-vanishing and site-sum-positivity
inputs on top of the with-nonzero package.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

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

end LatticeSystem.Quantum
