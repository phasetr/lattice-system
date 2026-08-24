import LatticeSystem.Math.ComplexVectorKernel

/-!
# Ladder invariance of a real expectation ratio

Model-agnostic linear algebra behind the `SU(2)` ladder argument for expectation values.  Let
`Sp Sm : Matrix ι ι ℂ` be an adjoint pair (`Smᴴ = Sp`), let `O : Matrix ι ι ℂ` commute with `Sp`,
and let `v` be an eigenvector of the raising-after-lowering product,
`(Sp * Sm) *ᵥ v = c • v`.  Writing `⟨a, b⟩ := star a ⬝ᵥ b`, the lowering step `v ↦ Sm *ᵥ v`
rescales the expectation of `O` by exactly the same scalar `c` that rescales the squared norm:

  `⟨Sm v, O (Sm v)⟩ = c · ⟨v, O v⟩`,   `‖Sm v‖² = c · ‖v‖²`.

The first identity is `ladder_expectation_cross`; the second is its `O = 1` instance.  Dividing
them gives `ladder_expectationRatioRe_invariant`: the real Rayleigh quotient
`⟨v, O v⟩.re / ‖v‖²` is unchanged by the lowering step whenever `Sm *ᵥ v ≠ 0`.

Derivation of the cross identity: `⟨Sm v, O (Sm v)⟩ = ⟨v, Smᴴ O Sm v⟩ = ⟨v, Sp O Sm v⟩` by the
matrix-adjoint dot-product law and `Smᴴ = Sp`; then `Sp O Sm = O (Sp Sm)` since `O` commutes with
`Sp`, and `Sp Sm` acts on `v` as the scalar `c`.  Reality of `c` is *not* a hypothesis: it follows
from the `O = 1` instance, because `‖Sm v‖²` and `‖v‖²` are real and the latter is nonzero.

Instantiated by the spin-`S` total ladder (`Quantum/SpinS/SU2ExpectationLadderInvariant.lean`) and
by the Hubbard-fermion total ladder
(`Fermion/JordanWigner/Hubbard/LiebFerrimagnetismLadderRatio.lean`); in both cases the scalar is
the Casimir rearrangement `c = γ − m² + m` on a joint `Ŝ³` / `(Ŝ)²` eigenvector.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).
-/

namespace LatticeSystem.Math

open Matrix

variable {ι : Type*} [Fintype ι]

/-- **Ladder-expectation cross identity.** For `O Sp Sm : Matrix ι ι ℂ` with `Smᴴ = Sp`, `O`
commuting with `Sp`, and `v` an eigenvector of `Sp * Sm` at the scalar `c`, the expectation of `O`
on the lowered vector `Sm *ᵥ v` is `c` times the expectation on `v`:
`⟨Sm v, O (Sm v)⟩ = c • ⟨v, O v⟩`, where `⟨a, b⟩ := star a ⬝ᵥ b`. -/
theorem ladder_expectation_cross (O Sp Sm : Matrix ι ι ℂ) (hadj : Smᴴ = Sp)
    (hcomm : Commute O Sp) {c : ℂ} {v : ι → ℂ}
    (hscal : (Sp * Sm).mulVec v = c • v) :
    star (Sm.mulVec v) ⬝ᵥ O.mulVec (Sm.mulVec v) = c • (star v ⬝ᵥ O.mulVec v) := by
  -- Move the left factor across the dot product: `⟨Sm v, O Sm v⟩ = ⟨v, Smᴴ (O Sm v)⟩`.
  rw [star_mulVec_dotProduct, hadj]
  have hmul : Sp * O * Sm = O * (Sp * Sm) := by rw [← hcomm, mul_assoc]
  have hvec : Sp.mulVec (O.mulVec (Sm.mulVec v)) = c • O.mulVec v := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmul, ← Matrix.mulVec_mulVec, hscal,
      Matrix.mulVec_smul]
  rw [hvec, dotProduct_smul, smul_eq_mul]

/-- **Ladder invariance of the real expectation ratio.** Under the hypotheses of
`ladder_expectation_cross` together with `Sm *ᵥ v ≠ 0`, numerator and denominator of the real
Rayleigh quotient of `O` pick up the same real factor `c.re`, so the quotient is preserved by the
lowering step:
`⟨Sm v, O (Sm v)⟩.re / ⟨Sm v, Sm v⟩.re = ⟨v, O v⟩.re / ⟨v, v⟩.re`. -/
theorem ladder_expectationRatioRe_invariant (O Sp Sm : Matrix ι ι ℂ) (hadj : Smᴴ = Sp)
    (hcomm : Commute O Sp) {c : ℂ} {v : ι → ℂ}
    (hscal : (Sp * Sm).mulVec v = c • v) (hne : Sm.mulVec v ≠ 0) :
    (star (Sm.mulVec v) ⬝ᵥ O.mulVec (Sm.mulVec v)).re /
        (star (Sm.mulVec v) ⬝ᵥ Sm.mulVec v).re =
      (star v ⬝ᵥ O.mulVec v).re / (star v ⬝ᵥ v).re := by
  -- `1 : Matrix ι ι ℂ` (used only inside the proof) needs a `DecidableEq ι`.
  classical
  have hvne : v ≠ 0 := by
    intro h
    exact hne (by rw [h, Matrix.mulVec_zero])
  have hSm_pos : 0 < (star (Sm.mulVec v) ⬝ᵥ Sm.mulVec v).re := dotProduct_star_self_re_pos hne
  have hv_pos : 0 < (star v ⬝ᵥ v).re := dotProduct_star_self_re_pos hvne
  -- The `O = 1` instance of the cross identity is the squared-norm scaling `‖Sm v‖² = c ‖v‖²`.
  have hden : star (Sm.mulVec v) ⬝ᵥ Sm.mulVec v = c • (star v ⬝ᵥ v) := by
    have h1 := ladder_expectation_cross (1 : Matrix ι ι ℂ) Sp Sm hadj (Commute.one_left Sp) hscal
    simpa only [Matrix.one_mulVec] using h1
  -- `c` is real: it is the ratio of the two (real) squared norms.
  have hcim : c.im = 0 := by
    have h1 : (c • (star v ⬝ᵥ v)).im = 0 := by
      rw [← hden, star_dotProduct_self_eq, Complex.ofReal_im]
    rw [star_dotProduct_self_eq v, smul_eq_mul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add] at h1
    rcases mul_eq_zero.mp h1 with hci | hsum
    · exact hci
    · exfalso
      refine hv_pos.ne' ?_
      rw [star_dotProduct_self_eq v, Complex.ofReal_re, hsum]
  have hnum_re : (star (Sm.mulVec v) ⬝ᵥ O.mulVec (Sm.mulVec v)).re =
      c.re * (star v ⬝ᵥ O.mulVec v).re := by
    rw [ladder_expectation_cross O Sp Sm hadj hcomm hscal, smul_eq_mul, Complex.mul_re, hcim,
      zero_mul, sub_zero]
  have hden_re : (star (Sm.mulVec v) ⬝ᵥ Sm.mulVec v).re = c.re * (star v ⬝ᵥ v).re := by
    rw [hden, smul_eq_mul, Complex.mul_re, hcim, zero_mul, sub_zero]
  have hcre_ne : c.re ≠ 0 := by
    intro h0
    rw [hden_re, h0, zero_mul] at hSm_pos
    exact lt_irrefl 0 hSm_pos
  rw [hnum_re, hden_re, mul_div_mul_left _ _ hcre_ne]

end LatticeSystem.Math
