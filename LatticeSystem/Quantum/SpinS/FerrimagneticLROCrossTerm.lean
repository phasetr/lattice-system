import LatticeSystem.Quantum.SpinS.FerrimagneticLROComponentAlgebra
import LatticeSystem.Quantum.SpinS.Problem25dSectorSupportedWrapper
import LatticeSystem.Quantum.SpinS.Problem25dLadderAdjointEquality

/-!
# Tasaki §4.1 (Theorem 4.4): the cross-term inequality (4.1.15)

This file proves the cross-term step of Tasaki's finite-volume proof of Theorem 4.4
(Shen–Qiu–Tian ferrimagnetic long-range order), the summed inequality feeding the chain
(4.1.16) (step 3 of the (4.1.16) argument, i.e. eq. (4.1.15)):

On the Marshall-positive sector ground state `Φ`, the *staggered* transverse double sum
dominates the *unstaggered* one in expectation,

  `⟨Φ, (Σ_{x,y} T_{x,y}) Φ⟩.re ≤ ⟨Φ, staggeredTransverseCasimirOpS Φ⟩.re`,

where `T_{x,y} = Ŝ_x^{(1)} Ŝ_y^{(1)} + Ŝ_x^{(2)} Ŝ_y^{(2)}` is the transverse two-spin operator and
`staggeredTransverseCasimirOpS = Σ_{x,y} ε_x ε_y T_{x,y}` (PR1, with
`ε_x = bipartiteGaugeSign A x`).

The mechanism is Tasaki's Marshall-sign positivity (Problem 2.5.d):

* on a same-sublattice pair `ε_x ε_y = +1`, so the staggered and unstaggered terms agree;
* on a cross-sublattice pair `ε_x ε_y = -1`, the transverse expectation `⟨Φ, T_{x,y} Φ⟩.re ≤ 0`
  (Marshall positivity), so `(ε_x ε_y - 1)⟨Φ, T_{x,y} Φ⟩.re = -2⟨Φ, T_{x,y} Φ⟩.re ≥ 0`.

Hence the difference `Σ_{x,y} (ε_x ε_y - 1) T_{x,y}` has non-negative expectation, which is the
content of (4.1.15).  The value-dependent assembly into the final chain (4.1.16) is left for the
capstone PR that discharges the axiom `shenQiuTian_ferrimagnetic_lro` in `FerrimagneticLRO.lean`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.4, eqs. (4.1.12)–(4.1.16), pp. 77–78; Problem 2.5.d, p. 40, solution
pp. 498–499.
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

/-! ## The summed cross-term inequality (4.1.15) -/

/-- **Per-pair staggered-vs-unstaggered transverse bound.**  For any pair, the transverse
expectation is bounded above by its staggered (gauge-signed) counterpart:
`⟨Φ, T_{x,y} Φ⟩.re ≤ (ε_x ε_y ⟨Φ, T_{x,y} Φ⟩).re`.  Same-sublattice pairs give `ε_x ε_y = +1`
(equality); cross-sublattice pairs give `ε_x ε_y = -1` with `⟨Φ, T_{x,y} Φ⟩.re ≤ 0`. -/
theorem twoSpinTransverseCorrelationS_le_staggered_of_marshall_sector
    (A : Λ → Bool) (x y : Λ) {M : ℕ} (c : magConfigS Λ N M → ℝ) (hc_pos : ∀ σ, 0 < c σ) :
    (twoSpinTransverseCorrelationS x y
        (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          marshallSignS A σ.1 * (c σ : ℂ)))).re ≤
      ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinTransverseCorrelationS x y
          (magSectorEmbedding (fun σ : magConfigS Λ N M =>
            marshallSignS A σ.1 * (c σ : ℂ)))).re := by
  set Φ : (Λ → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ : magConfigS Λ N M =>
      marshallSignS A σ.1 * (c σ : ℂ)) with hΦ
  by_cases hAxy : A x = A y
  · -- Same sublattice: the gauge sign is `+1`, so both sides agree.
    rw [bipartiteGaugeSign_mul_eq_one_of_same A hAxy, one_mul]
  · -- Cross sublattice: the gauge sign is `-1` and `⟨T⟩.re ≤ 0`.
    by_cases hxy : x = y
    · -- A x = A y when x = y contradicts `hAxy`.
      exact absurd (by rw [hxy]) hAxy
    · rw [bipartiteGaugeSign_mul_eq_neg_one_of_ne A hAxy]
      have hnonpos := twoSpinTransverseCorrelationS_re_nonpos_of_marshall_sector_cross
        A hxy hAxy c hc_pos
      rw [← hΦ] at hnonpos
      rw [show (-1 * twoSpinTransverseCorrelationS x y Φ).re =
          -(twoSpinTransverseCorrelationS x y Φ).re by simp]
      linarith

/-- **Real part of an expectation against a double-sum operator.**  For a `Λ`-indexed double sum of
operators, the real part of the expectation distributes as the double sum of the per-term
expectation real parts.  This bridges the summed operator `Σ_{x,y} T_{x,y}` to the per-pair
transverse correlations. -/
theorem dotProduct_sum_sum_mulVec_re_eq_sum
    (Φ : (Λ → Fin (N + 1)) → ℂ) (O : Λ → Λ → ManyBodyOpS Λ N) :
    (star Φ ⬝ᵥ ((∑ x : Λ, ∑ y : Λ, O x y).mulVec Φ)).re =
      ∑ x : Λ, ∑ y : Λ, (star Φ ⬝ᵥ ((O x y).mulVec Φ)).re := by
  rw [Matrix.sum_mulVec]
  rw [dotProduct_sum]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]

/-- **The summed cross-term inequality (4.1.15).**  On the Marshall-positive sector ground state
`Φ = magSectorEmbedding (σ ↦ marshallSignS A σ.1 * c σ)` with `c` strictly positive, the unstaggered
transverse double sum is dominated in expectation by the staggered one:

  `⟨Φ, (Σ_{x,y} T_{x,y}) Φ⟩.re ≤ ⟨Φ, staggeredTransverseCasimirOpS Φ⟩.re`.

This is the cross-term step (eq. (4.1.15)) feeding Tasaki's chain (4.1.16), assembled by summing the
per-pair bound `twoSpinTransverseCorrelationS_le_staggered_of_marshall_sector`. -/
theorem noStaggeringTransverse_expectation_le_staggeredTransverse_expectation_of_marshall_sector
    (A : Λ → Bool) {M : ℕ} (c : magConfigS Λ N M → ℝ) (hc_pos : ∀ σ, 0 < c σ)
    (Φ : (Λ → Fin (N + 1)) → ℂ)
    (hΦ : Φ = magSectorEmbedding (fun σ : magConfigS Λ N M =>
      marshallSignS A σ.1 * (c σ : ℂ))) :
    (star Φ ⬝ᵥ
        ((∑ x : Λ, ∑ y : Λ,
          (spinSSiteOp1 x N * spinSSiteOp1 y N +
            spinSSiteOp2 x N * spinSSiteOp2 y N)).mulVec Φ)).re ≤
      (star Φ ⬝ᵥ (staggeredTransverseCasimirOpS A N).mulVec Φ).re := by
  -- Rewrite both sides as double sums of per-pair real parts.
  rw [dotProduct_sum_sum_mulVec_re_eq_sum Φ
    (fun x y => spinSSiteOp1 x N * spinSSiteOp1 y N + spinSSiteOp2 x N * spinSSiteOp2 y N)]
  rw [show staggeredTransverseCasimirOpS A N =
      ∑ x : Λ, ∑ y : Λ,
        ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) •
          (spinSSiteOp1 x N * spinSSiteOp1 y N + spinSSiteOp2 x N * spinSSiteOp2 y N)) by
    unfold staggeredTransverseCasimirOpS bipartiteGaugeSign; rfl]
  rw [dotProduct_sum_sum_mulVec_re_eq_sum Φ
    (fun x y => (bipartiteGaugeSign A x * bipartiteGaugeSign A y) •
      (spinSSiteOp1 x N * spinSSiteOp1 y N + spinSSiteOp2 x N * spinSSiteOp2 y N))]
  -- Compare termwise.
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  -- The per-pair scaled expectation real part matches the gauge-signed correlation.
  have hscaled :
      (star Φ ⬝ᵥ (((bipartiteGaugeSign A x * bipartiteGaugeSign A y) •
          (spinSSiteOp1 x N * spinSSiteOp1 y N +
            spinSSiteOp2 x N * spinSSiteOp2 y N)).mulVec Φ)).re =
        ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
          twoSpinTransverseCorrelationS x y Φ).re := by
    unfold twoSpinTransverseCorrelationS
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [hscaled]
  -- Reduce to the per-pair bound, with `Φ` the sector embedding.
  rw [show (star Φ ⬝ᵥ ((spinSSiteOp1 x N * spinSSiteOp1 y N +
        spinSSiteOp2 x N * spinSSiteOp2 y N).mulVec Φ)).re =
      (twoSpinTransverseCorrelationS x y Φ).re by rfl]
  rw [hΦ]
  exact twoSpinTransverseCorrelationS_le_staggered_of_marshall_sector A x y c hc_pos

end LatticeSystem.Quantum
