import LatticeSystem.Quantum.SpinS.AxisSwapLadderEntry
import LatticeSystem.Quantum.SpinS.MarshallSign
import LatticeSystem.Quantum.SpinS.Problem25dCorrelationSignBridge

/-!
# Tasaki Problem 2.5.d: ladder-correlation positivity expansion

This module continues the Problem 2.5.d correlation-sign formalization by
isolating the finite-basis positivity step in Tasaki's solution.  Once the
signed terms in the configuration-basis expansion of
`⟨Φ, Ŝ_x^+ Ŝ_y^- Φ⟩` are non-negative and one term is strictly positive, the
signed ladder expectation has positive real part.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, and solution p. 498, equations
(S.22)--(S.23).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} {N : ℕ}

/-! ## Ladder correlation -/

/-- The transverse ladder correlation expectation
`⟨Φ, (Ŝ_x^+ Ŝ_y^-) Φ⟩` for a spin-`S` many-body state. -/
noncomputable def twoSpinPlusMinusCorrelationS (x y : V)
    [Fintype V] [DecidableEq V]
    (Φ : (V → Fin (N + 1)) → ℂ) : ℂ :=
  dotProduct (star Φ)
    (((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)) : ManyBodyOpS V N).mulVec Φ)

/-! ## Finite-basis signed-positivity expansion -/

/-- Expand a signed matrix expectation into its configuration-basis double sum,
keeping the real part outside the individual terms. -/
theorem signedExpectation_re_eq_sum
    {ι : Type*} [Fintype ι]
    (g : ℂ) (O : Matrix ι ι ℂ) (Φ : ι → ℂ) :
    (g * dotProduct (star Φ) (O.mulVec Φ)).re =
      ∑ i : ι, ∑ j : ι, (g * star (Φ i) * O i j * Φ j).re := by
  change (g * ∑ i : ι, star (Φ i) * (∑ j : ι, O i j * Φ j)).re =
    ∑ i : ι, ∑ j : ι, (g * star (Φ i) * O i j * Φ j).re
  rw [show g * (∑ i : ι, star (Φ i) * (∑ j : ι, O i j * Φ j)) =
      ∑ i : ι, g * (star (Φ i) * (∑ j : ι, O i j * Φ j)) by
    rw [Finset.mul_sum]]
  have hsum_re : ∀ f : ι → ℂ, (∑ i : ι, f i).re = ∑ i : ι, (f i).re := by
    intro f
    simp
  rw [hsum_re]
  apply Finset.sum_congr rfl
  intro i _
  rw [show star (Φ i) * (∑ j : ι, O i j * Φ j) =
      ∑ j : ι, star (Φ i) * (O i j * Φ j) by
    rw [Finset.mul_sum]]
  rw [show g * (∑ j : ι, star (Φ i) * (O i j * Φ j)) =
      ∑ j : ι, g * (star (Φ i) * (O i j * Φ j)) by
    rw [Finset.mul_sum]]
  rw [hsum_re]
  apply Finset.sum_congr rfl
  intro j _
  ring_nf

/-- If every signed term in the configuration-basis expansion of a matrix
expectation has non-negative real part and at least one term has positive real
part, then the full signed expectation has positive real part. -/
theorem signedExpectation_re_pos_of_term_re_nonneg_exists_pos
    {ι : Type*} [Fintype ι]
    (g : ℂ) (O : Matrix ι ι ℂ) (Φ : ι → ℂ)
    (hterm_nonneg : ∀ i j : ι, 0 ≤ (g * star (Φ i) * O i j * Φ j).re)
    (hterm_pos : ∃ i j : ι, 0 < (g * star (Φ i) * O i j * Φ j).re) :
    0 < (g * dotProduct (star Φ) (O.mulVec Φ)).re := by
  rw [signedExpectation_re_eq_sum]
  obtain ⟨i₀, j₀, hpos⟩ := hterm_pos
  refine Finset.sum_pos' ?_ ?_
  · intro i _
    exact Finset.sum_nonneg (fun j _ => hterm_nonneg i j)
  · refine ⟨i₀, Finset.mem_univ i₀, ?_⟩
    refine Finset.sum_pos' ?_ ?_
    · intro j _
      exact hterm_nonneg i₀ j
    · exact ⟨j₀, Finset.mem_univ j₀, hpos⟩

/-- Coefficient form of the signed-positivity expansion: if
`Φ i = s i * c i` with real strictly positive coefficients `c i`, and the
signed matrix entries `g * s i * O i j * s j` are all non-negative with one
strictly positive entry, then the signed expectation is strictly positive. -/
theorem signedExpectation_re_pos_of_positive_coefficients
    {ι : Type*} [Fintype ι]
    (g : ℂ) (O : Matrix ι ι ℂ) (s : ι → ℂ) (c : ι → ℝ)
    (hs_star : ∀ i, star (s i) = s i)
    (hc_pos : ∀ i, 0 < c i)
    (hentry_nonneg : ∀ i j : ι, 0 ≤ (g * s i * O i j * s j).re)
    (hentry_pos : ∃ i j : ι, 0 < (g * s i * O i j * s j).re) :
    0 < (g * dotProduct (star (fun i => s i * (c i : ℂ)))
      (O.mulVec (fun i => s i * (c i : ℂ)))).re := by
  refine signedExpectation_re_pos_of_term_re_nonneg_exists_pos g O
    (fun i => s i * (c i : ℂ)) ?_ ?_
  · intro i j
    have hscale :
        (g * star (s i * (c i : ℂ)) * O i j * (s j * (c j : ℂ))).re =
          (c i * c j) * (g * s i * O i j * s j).re := by
      rw [StarMul.star_mul, hs_star i]
      simp
      ring_nf
    rw [hscale]
    exact mul_nonneg (le_of_lt (mul_pos (hc_pos i) (hc_pos j))) (hentry_nonneg i j)
  · obtain ⟨i, j, hpos⟩ := hentry_pos
    refine ⟨i, j, ?_⟩
    have hscale :
        (g * star (s i * (c i : ℂ)) * O i j * (s j * (c j : ℂ))).re =
          (c i * c j) * (g * s i * O i j * s j).re := by
      rw [StarMul.star_mul, hs_star i]
      simp
      ring_nf
    rw [hscale]
    exact mul_pos (mul_pos (hc_pos i) (hc_pos j)) hpos

/-- Problem 2.5.d ladder signed-positivity wrapper: if the bipartite-gauge
signed terms in the `Ŝ_x^+ Ŝ_y^-` expectation expansion are all non-negative
and one term is strictly positive, then the bipartite-gauge-signed ladder
correlation has positive real part. -/
theorem twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_term_re_nonneg_exists_pos
    [Fintype V] [DecidableEq V]
    (A : V → Bool) (x y : V) (Φ : (V → Fin (N + 1)) → ℂ)
    (hterm_nonneg : ∀ σ τ : V → Fin (N + 1),
      0 ≤ ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        star (Φ σ) *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ) *
        Φ τ).re)
    (hterm_pos : ∃ σ τ : V → Fin (N + 1),
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        star (Φ σ) *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ) *
        Φ τ).re) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinPlusMinusCorrelationS x y Φ).re := by
  exact signedExpectation_re_pos_of_term_re_nonneg_exists_pos
    (bipartiteGaugeSign A x * bipartiteGaugeSign A y)
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N))
    Φ hterm_nonneg hterm_pos

/-- Problem 2.5.d Marshall-coefficient ladder signed-positivity wrapper:
for the Marshall-gauge state `σ ↦ marshallSignS A σ * c σ` with strictly
positive real coefficients, signed non-negative ladder matrix entries and one
strictly positive ladder matrix entry imply a positive bipartite-gauge-signed
`Ŝ_x^+ Ŝ_y^-` correlation. -/
theorem twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_marshall_coefficients
    [Fintype V] [DecidableEq V]
    (A : V → Bool) (x y : V) (c : (V → Fin (N + 1)) → ℝ)
    (hc_pos : ∀ σ, 0 < c σ)
    (hentry_nonneg : ∀ σ τ : V → Fin (N + 1),
      0 ≤ ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ) *
        marshallSignS A τ).re)
    (hentry_pos : ∃ σ τ : V → Fin (N + 1),
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ) *
        marshallSignS A τ).re) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinPlusMinusCorrelationS x y
        (fun σ => marshallSignS A σ * (c σ : ℂ))).re := by
  exact signedExpectation_re_pos_of_positive_coefficients
    (bipartiteGaugeSign A x * bipartiteGaugeSign A y)
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N))
    (marshallSignS A) c (marshallSignS_star A) hc_pos hentry_nonneg hentry_pos

end LatticeSystem.Quantum
