import LatticeSystem.Quantum.SpinS.FerrimagneticLROCrossTermCore
import LatticeSystem.Quantum.SpinS.FerrimagneticLROComponentAlgebra

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
