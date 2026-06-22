import LatticeSystem.Quantum.SpinS.Problem25dSectorSupportedWrapper
import LatticeSystem.Quantum.SpinS.Problem25dLadderAdjointEquality

/-!
# Ferrimagnetic LRO cross-term: transverse correlation foundation

Foundational layer extracted from `FerrimagneticLROCrossTerm.lean` for build speed (Tasaki
§4.1, eq. (4.1.15)).  This file develops the transverse two-spin correlation, the non-strict
signed ladder positivity on a Marshall sector, and the per-pair transverse expectation sign.

The summed cross-term inequality (4.1.15) is kept in the capstone module
`FerrimagneticLROCrossTerm.lean`.
-/

namespace LatticeSystem.Quantum

open Matrix

open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## The transverse two-spin correlation -/

/-- The **transverse two-spin correlation expectation**
`⟨Φ, (Ŝ_x^{(1)} Ŝ_y^{(1)} + Ŝ_x^{(2)} Ŝ_y^{(2)}) Φ⟩` for a spin-`S` many-body state.  This is the
expectation of the transverse two-spin operator `T_{x,y}` whose staggered double sum is
`staggeredTransverseCasimirOpS` (PR1, eq. (4.1.12)). -/
noncomputable def twoSpinTransverseCorrelationS (x y : Λ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) : ℂ :=
  dotProduct (star Φ)
    ((spinSSiteOp1 x N * spinSSiteOp1 y N + spinSSiteOp2 x N * spinSSiteOp2 y N).mulVec Φ)

/-- **Transverse operator = half the symmetrized ladder operator.**  The `(1,1)+(2,2)`-component
two-spin operator equals `½(Ŝ_x^+ Ŝ_y^- + Ŝ_x^- Ŝ_y^+)`, obtained by subtracting the longitudinal
`Ŝ_x^{(3)} Ŝ_y^{(3)}` term from both forms of `Ŝ_x · Ŝ_y` (`spinSDot_def` and
`spinSDot_eq_plus_minus`). -/
theorem spinSSiteOp1_mul_add_spinSSiteOp2_mul_eq_half_ladder (x y : Λ) (N : ℕ) :
    (spinSSiteOp1 x N * spinSSiteOp1 y N + spinSSiteOp2 x N * spinSSiteOp2 y N
        : ManyBodyOpS Λ N) =
      (1 / 2 : ℂ) •
        (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) +
          onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) := by
  -- `S1S1 + S2S2 + S3S3 = ½(S⁺S⁻ + S⁻S⁺) + S3S3`, so cancel `S3S3`.
  have hkey :
      (spinSSiteOp1 x N * spinSSiteOp1 y N + spinSSiteOp2 x N * spinSSiteOp2 y N
          : ManyBodyOpS Λ N) +
        onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) =
      (1 / 2 : ℂ) •
        (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) +
          onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) +
        onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) := by
    simp only [spinSSiteOp1, spinSSiteOp2]
    rw [← spinSDot_eq_plus_minus, ← spinSDot_def]
  exact add_right_cancel hkey

/-- **Transverse correlation as the symmetrized ladder pair.**  The transverse two-spin correlation
is `½(twoSpinPlusMinusCorrelationS + twoSpinMinusPlusCorrelationS)`, obtained by applying the
operator identity `spinSSiteOp1_mul_add_spinSSiteOp2_mul_eq_half_ladder` inside the expectation. -/
theorem twoSpinTransverseCorrelationS_eq_half_ladder (x y : Λ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) :
    twoSpinTransverseCorrelationS x y Φ =
      (1 / 2 : ℂ) *
        (twoSpinPlusMinusCorrelationS x y Φ + twoSpinMinusPlusCorrelationS x y Φ) := by
  unfold twoSpinTransverseCorrelationS twoSpinPlusMinusCorrelationS twoSpinMinusPlusCorrelationS
  rw [spinSSiteOp1_mul_add_spinSSiteOp2_mul_eq_half_ladder]
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.add_mulVec, dotProduct_add, smul_eq_mul]

/-! ## Non-strict signed ladder positivity on a Marshall sector -/

/-- **Non-strict signed expectation positivity.**  If every term in the configuration-basis
expansion of a signed matrix expectation has non-negative real part, then the full signed
expectation has non-negative real part.  This is the non-strict companion of
`signedExpectation_re_pos_of_term_re_nonneg_exists_pos`, needed for the cross-term `≤` bound (no
strict witness is required). -/
theorem signedExpectation_re_nonneg_of_term_re_nonneg
    {ι : Type*} [Fintype ι]
    (g : ℂ) (O : Matrix ι ι ℂ) (Φ : ι → ℂ)
    (hterm_nonneg : ∀ i j : ι, 0 ≤ (g * star (Φ i) * O i j * Φ j).re) :
    0 ≤ (g * dotProduct (star Φ) (O.mulVec Φ)).re := by
  rw [signedExpectation_re_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm_nonneg i j

/-- **Non-strict bipartite-signed `Ŝ_x^+ Ŝ_y^-` positivity on a Marshall sector.**  For a
cross-sublattice pair, the bipartite-gauge / Marshall-signed `Ŝ_x^+ Ŝ_y^-` correlation of the
zero-extended Marshall sector vector has non-negative real part.  Unlike the strict sector wrapper
`twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_marshall_sector_cross`, this requires no
strict sector witness, only the per-entry non-negativity of Tasaki's eq. (S.23). -/
theorem twoSpinPlusMinusCorrelationS_bipartite_signed_re_nonneg_of_marshall_sector_cross
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    {M : ℕ} (c : magConfigS Λ N M → ℝ) (hc_pos : ∀ σ, 0 < c σ) :
    0 ≤ ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinPlusMinusCorrelationS x y
        (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          marshallSignS A σ.1 * (c σ : ℂ)))).re := by
  classical
  let g : ℂ := bipartiteGaugeSign A x * bipartiteGaugeSign A y
  let O : ManyBodyOpS Λ N :=
    onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
  let Φ : (Λ → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ : magConfigS Λ N M =>
      marshallSignS A σ.1 * (c σ : ℂ))
  -- The per-entry sign input (Tasaki eq. (S.23)).
  have hentry := twoSpinPlusMinus_ladder_signed_entry_re_nonneg_of_bipartite_ne (N := N) A hxy hAxy
  -- Convert to the embedded sector vector entrywise.
  have hterm : ∀ σ τ : Λ → Fin (N + 1),
      0 ≤ (g * star (Φ σ) * O σ τ * Φ τ).re := by
    intro σ τ
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
          (by simpa [g, O] using hentry σ τ)
      · rw [show Φ τ = 0 by simp [Φ, magSectorEmbedding_apply_of_not_mem _ hτ]]
        simp
    · rw [show Φ σ = 0 by simp [Φ, magSectorEmbedding_apply_of_not_mem _ hσ]]
      simp
  -- Feed into the generic non-strict expectation lemma.
  exact signedExpectation_re_nonneg_of_term_re_nonneg g O Φ hterm

/-! ## Per-pair transverse expectation sign -/

/-- **Per-pair transverse non-positivity on the Marshall sector.**  For a cross-sublattice pair, the
transverse two-spin correlation of the zero-extended Marshall sector vector has non-positive real
part.  This is the per-pair content of Tasaki's (4.1.15): `⟨Φ, T_{x,y} Φ⟩.re ≤ 0`.

Proof: by `twoSpinTransverseCorrelationS_eq_half_ladder` and the ladder-adjoint equality the
transverse real part equals `twoSpinPlusMinusCorrelationS.re`; on a cross pair the bipartite gauge
sign is `-1`, so the non-strict signed positivity above gives `0 ≤ -plusMinus.re`. -/
theorem twoSpinTransverseCorrelationS_re_nonpos_of_marshall_sector_cross
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    {M : ℕ} (c : magConfigS Λ N M → ℝ) (hc_pos : ∀ σ, 0 < c σ) :
    (twoSpinTransverseCorrelationS x y
      (magSectorEmbedding (fun σ : magConfigS Λ N M =>
        marshallSignS A σ.1 * (c σ : ℂ)))).re ≤ 0 := by
  set Φ : (Λ → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ : magConfigS Λ N M =>
      marshallSignS A σ.1 * (c σ : ℂ)) with hΦ
  -- The signed plusMinus and minusPlus real parts coincide (ladder adjoint).
  have hadj := bipartite_signed_twoSpinMinusPlusCorrelationS_re_eq_plusMinus A hxy hAxy Φ
  -- Non-strict signed plusMinus positivity.
  have hpm := twoSpinPlusMinusCorrelationS_bipartite_signed_re_nonneg_of_marshall_sector_cross
    A hxy hAxy c hc_pos
  rw [← hΦ] at hpm
  -- On a cross pair, the bipartite gauge sign is `-1`.
  have hg : bipartiteGaugeSign A x * bipartiteGaugeSign A y = -1 :=
    bipartiteGaugeSign_mul_eq_neg_one_of_ne A hAxy
  rw [hg] at hpm hadj
  -- `0 ≤ (-1 * plusMinus).re = -plusMinus.re`, so `plusMinus.re ≤ 0`.
  have hpm_nonpos : (twoSpinPlusMinusCorrelationS x y Φ).re ≤ 0 := by
    have : (-1 * twoSpinPlusMinusCorrelationS x y Φ).re =
        -(twoSpinPlusMinusCorrelationS x y Φ).re := by simp
    rw [this] at hpm; linarith
  have hmp_nonpos : (twoSpinMinusPlusCorrelationS x y Φ).re ≤ 0 := by
    have hmp_eq : (twoSpinMinusPlusCorrelationS x y Φ).re =
        (twoSpinPlusMinusCorrelationS x y Φ).re := by
      have e1 : (-1 * twoSpinMinusPlusCorrelationS x y Φ).re =
          -(twoSpinMinusPlusCorrelationS x y Φ).re := by simp
      have e2 : (-1 * twoSpinPlusMinusCorrelationS x y Φ).re =
          -(twoSpinPlusMinusCorrelationS x y Φ).re := by simp
      rw [e1, e2] at hadj; linarith
    rw [hmp_eq]; exact hpm_nonpos
  -- Combine via the half-ladder decomposition of the transverse correlation.
  rw [twoSpinTransverseCorrelationS_eq_half_ladder]
  rw [show ((1 / 2 : ℂ) *
        (twoSpinPlusMinusCorrelationS x y Φ + twoSpinMinusPlusCorrelationS x y Φ)).re =
      (1 / 2 : ℝ) * ((twoSpinPlusMinusCorrelationS x y Φ).re +
        (twoSpinMinusPlusCorrelationS x y Φ).re) by simp]
  nlinarith [hpm_nonpos, hmp_nonpos]

end LatticeSystem.Quantum
