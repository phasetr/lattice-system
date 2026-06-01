import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.Problem25dGroundStatePhaseWrapper

/-!
# Tasaki Problem 2.5.d: sector-supported correlation wrapper

The preceding Problem 2.5.d wrappers used a full-space coefficient function
that is strictly positive on every configuration.  The actual
Marshall--Lieb--Mattis Perron--Frobenius ground vector is strictly positive on
one magnetization sector and is zero-extended to the full configuration space.
This module supplies the corresponding sector-supported positivity wrapper.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, and solution pp. 498--499, equations
(S.22)--(S.23).
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Sector-supported ladder positivity -/

/-- Sector-supported Problem 2.5.d ladder positivity: if a
Marshall-positive sector vector is embedded by zero-extension into the full
configuration space, the signed `S_x^+ S_y^-` expectation is positive as soon
as all signed full-space matrix entries are non-negative and one strictly
positive signed entry occurs within the sector. -/
theorem twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_marshall_sector_coefficients
    (A : V → Bool) (x y : V) {M : ℕ} (c : magConfigS V N M → ℝ)
    (hc_pos : ∀ σ, 0 < c σ)
    (hentry_nonneg : ∀ σ τ : V → Fin (N + 1),
      0 ≤ ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ) *
        marshallSignS A τ).re)
    (hentry_pos : ∃ σ τ : magConfigS V N M,
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ.1 *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N)
          σ.1 τ.1) *
        marshallSignS A τ.1).re) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinPlusMinusCorrelationS x y
        (magSectorEmbedding (fun σ : magConfigS V N M =>
          marshallSignS A σ.1 * (c σ : ℂ)))).re := by
  classical
  let g : ℂ := bipartiteGaugeSign A x * bipartiteGaugeSign A y
  let O : ManyBodyOpS V N :=
    onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
  let Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ : magConfigS V N M =>
      marshallSignS A σ.1 * (c σ : ℂ))
  refine twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_term_re_nonneg_exists_pos
    A x y Φ ?_ ?_
  · intro σ τ
    by_cases hσ : magSumS σ = M
    · by_cases hτ : magSumS τ = M
      · have hscale :
            (g * star (Φ σ) * O σ τ * Φ τ).re =
              (c ⟨σ, hσ⟩ * c ⟨τ, hτ⟩) *
                (g * marshallSignS A σ * O σ τ * marshallSignS A τ).re := by
          rw [show Φ σ = marshallSignS A σ * (c ⟨σ, hσ⟩ : ℂ) by
            simp [Φ, magSectorEmbedding_apply_of_mem _ hσ]]
          rw [show Φ τ = marshallSignS A τ * (c ⟨τ, hτ⟩ : ℂ) by
            simp [Φ, magSectorEmbedding_apply_of_mem _ hτ]]
          rw [StarMul.star_mul, marshallSignS_star A σ]
          simp
          ring_nf
        rw [hscale]
        exact mul_nonneg (le_of_lt (mul_pos (hc_pos ⟨σ, hσ⟩) (hc_pos ⟨τ, hτ⟩)))
          (by simpa [g, O] using hentry_nonneg σ τ)
      · rw [show Φ τ = 0 by
          simp [Φ, magSectorEmbedding_apply_of_not_mem _ hτ]]
        simp
    · rw [show Φ σ = 0 by
        simp [Φ, magSectorEmbedding_apply_of_not_mem _ hσ]]
      simp
  · obtain ⟨σ, τ, hpos⟩ := hentry_pos
    refine ⟨σ.1, τ.1, ?_⟩
    have hscale :
        (g * star (Φ σ.1) * O σ.1 τ.1 * Φ τ.1).re =
          (c σ * c τ) *
            (g * marshallSignS A σ.1 * O σ.1 τ.1 * marshallSignS A τ.1).re := by
      rw [show Φ σ.1 = marshallSignS A σ.1 * (c σ : ℂ) by
        simp [Φ, magSectorEmbedding_apply_subtype]]
      rw [show Φ τ.1 = marshallSignS A τ.1 * (c τ : ℂ) by
        simp [Φ, magSectorEmbedding_apply_subtype]]
      rw [StarMul.star_mul, marshallSignS_star A σ.1]
      simp
      ring_nf
    rw [hscale]
    exact mul_pos (mul_pos (hc_pos σ) (hc_pos τ)) (by simpa [g, O] using hpos)

/-- Cross-sublattice specialization of the sector-supported ladder positivity
wrapper.  The strict positive entry is supplied as a sector-local witness. -/
theorem twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_marshall_sector_cross
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    {M : ℕ} (c : magConfigS V N M → ℝ) (hc_pos : ∀ σ, 0 < c σ)
    (hentry_pos : ∃ σ τ : magConfigS V N M,
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ.1 *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N)
          σ.1 τ.1) *
        marshallSignS A τ.1).re) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinPlusMinusCorrelationS x y
        (magSectorEmbedding (fun σ : magConfigS V N M =>
          marshallSignS A σ.1 * (c σ : ℂ)))).re := by
  exact twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_marshall_sector_coefficients
    A x y c hc_pos
    (twoSpinPlusMinus_ladder_signed_entry_re_nonneg_of_bipartite_ne A hxy hAxy)
    hentry_pos

/-! ## Sector-supported dot-product wrappers -/

/-- Sector-supported Problem 2.5.d package after the component equalities:
strictly positive Marshall coefficients on one magnetization sector, together
with a sector-local strict ladder entry, imply signed dot-product positivity
for the zero-extended sector vector. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_sector_cross_components
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    {M : ℕ} (c : magConfigS V N M → ℝ) (hc_pos : ∀ σ, 0 < c σ)
    (hentry_pos : ∃ σ τ : magConfigS V N M,
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ.1 *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N)
          σ.1 τ.1) *
        marshallSignS A τ.1).re)
    (hmp_eq :
      ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinMinusPlusCorrelationS x y
          (magSectorEmbedding (fun σ : magConfigS V N M =>
            marshallSignS A σ.1 * (c σ : ℂ)))).re =
      ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinPlusMinusCorrelationS x y
          (magSectorEmbedding (fun σ : magConfigS V N M =>
            marshallSignS A σ.1 * (c σ : ℂ)))).re)
    (hzz_eq :
      ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinZZCorrelationS x y
          (magSectorEmbedding (fun σ : magConfigS V N M =>
            marshallSignS A σ.1 * (c σ : ℂ)))).re =
      (1 / 2 : ℝ) * ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinPlusMinusCorrelationS x y
          (magSectorEmbedding (fun σ : magConfigS V N M =>
            marshallSignS A σ.1 * (c σ : ℂ)))).re) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y
        (magSectorEmbedding (fun σ : magConfigS V N M =>
          marshallSignS A σ.1 * (c σ : ℂ)))).re := by
  exact twoSpinCorrelationS_bipartite_signed_re_pos_of_ladder_component_equalities
    A x y
    (magSectorEmbedding (fun σ : magConfigS V N M => marshallSignS A σ.1 * (c σ : ℂ)))
    (twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_marshall_sector_cross
      A hxy hAxy c hc_pos hentry_pos)
    hmp_eq hzz_eq

/-- Sector-supported Problem 2.5.d package after the longitudinal component
equality: axis-swap and z-axis rotation phase invariance transfer the
sector-supported ladder positivity to signed dot-product positivity. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_sector_cross_axis_phases
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    {M : ℕ} (c : magConfigS V N M → ℝ) (hc_pos : ∀ σ, 0 < c σ)
    (hentry_pos : ∃ σ τ : magConfigS V N M,
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ.1 *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N)
          σ.1 τ.1) *
        marshallSignS A τ.1).re)
    (cswap crot : ℂ)
    (hΦswap :
      ((axisSwapUnitarySSpinS N).tensorInv V).mulVec
          (magSectorEmbedding (fun σ : magConfigS V N M =>
            marshallSignS A σ.1 * (c σ : ℂ))) =
        cswap • (magSectorEmbedding (fun σ : magConfigS V N M =>
          marshallSignS A σ.1 * (c σ : ℂ))))
    (hcswap : star cswap * cswap = 1)
    (hΦrot :
      (manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2))).mulVec
          (magSectorEmbedding (fun σ : magConfigS V N M =>
            marshallSignS A σ.1 * (c σ : ℂ))) =
        crot • (magSectorEmbedding (fun σ : magConfigS V N M =>
          marshallSignS A σ.1 * (c σ : ℂ))))
    (hcrot : star crot * crot = 1) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y
        (magSectorEmbedding (fun σ : magConfigS V N M =>
          marshallSignS A σ.1 * (c σ : ℂ)))).re := by
  exact twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_sector_cross_components
    A hxy hAxy c hc_pos hentry_pos
    (bipartite_signed_twoSpinMinusPlusCorrelationS_re_eq_plusMinus
      A hxy hAxy
      (magSectorEmbedding (fun σ : magConfigS V N M => marshallSignS A σ.1 * (c σ : ℂ))))
    (bipartite_signed_twoSpinZZCorrelationS_re_eq_half_plusMinus_of_axis_phases
      A hxy hAxy
      (magSectorEmbedding (fun σ : magConfigS V N M => marshallSignS A σ.1 * (c σ : ℂ)))
      cswap crot hΦswap hcswap hΦrot hcrot)

/-- Sector-supported ground-state phase wrapper: a normalized non-zero
Marshall-positive sector eigenvector, embedded by zero-extension into the full
configuration space, supplies the axis phases required by the sector-supported
Problem 2.5.d signed dot-product positivity wrapper. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_sector_cross_eigenphase
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    {M : ℕ} (J : V → V → ℂ) (μ : ℂ)
    (c : magConfigS V N M → ℝ) (hc_pos : ∀ σ, 0 < c σ)
    (hentry_pos : ∃ σ τ : magConfigS V N M,
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ.1 *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N)
          σ.1 τ.1) *
        marshallSignS A τ.1).re)
    (huniq : finrank ℂ ↥(End.eigenspace
      (Matrix.toLin' (heisenbergHamiltonianS J N)) μ) ≤ 1)
    (hΦ_ne :
      (magSectorEmbedding (fun σ : magConfigS V N M =>
        marshallSignS A σ.1 * (c σ : ℂ))) ≠ 0)
    (hΦnorm :
      dotProduct
        (star (magSectorEmbedding (fun σ : magConfigS V N M =>
          marshallSignS A σ.1 * (c σ : ℂ))))
        (magSectorEmbedding (fun σ : magConfigS V N M =>
          marshallSignS A σ.1 * (c σ : ℂ))) = 1)
    (hΦeig :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun σ : magConfigS V N M =>
            marshallSignS A σ.1 * (c σ : ℂ))) =
        μ • (magSectorEmbedding (fun σ : magConfigS V N M =>
          marshallSignS A σ.1 * (c σ : ℂ)))) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y
        (magSectorEmbedding (fun σ : magConfigS V N M =>
          marshallSignS A σ.1 * (c σ : ℂ)))).re := by
  obtain ⟨cswap, hswap, hcswap⟩ :=
    exists_phase_unit_of_heisenbergHamiltonianS_axisSwapUnitarySSpinS_tensorInv
      (V := V) (N := N) J μ huniq hΦ_ne hΦnorm hΦeig
  obtain ⟨crot, hrot, hcrot⟩ :=
    exists_phase_unit_of_heisenbergHamiltonianS_manyBodySpinSRot3
      (V := V) (N := N) J μ (Real.pi / 2) huniq hΦ_ne hΦnorm hΦeig
  exact twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_sector_cross_axis_phases
    A hxy hAxy c hc_pos hentry_pos cswap crot hswap hcswap hrot hcrot

end LatticeSystem.Quantum
