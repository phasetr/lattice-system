import LatticeSystem.Quantum.SpinS.Theorem23TotalLoweringNonvanishing
import LatticeSystem.Math.ComplexVectorKernel

/-!
# SU(2)-invariant operator expectations are total-ladder invariant
(Issue #4604, universal-form transfer of Tasaki Theorem 4.4, ingredient (b))

For an operator `O : ManyBodyOpS V N` that is SU(2)-invariant — i.e. it commutes
with the total raising and lowering operators `Ŝ⁺_tot` and `Ŝ⁻_tot` — and a joint
`Ŝ³_tot` / Casimir `(Ŝ_tot)²` eigenvector `v` (with eigenvalues `m` and `γ`), the
complex expectation of `O` along the once-lowered vector `Ŝ⁻_tot v` scales by the
*same* real factor `c = γ − m² + m` as the squared norm:

  `⟨Ŝ⁻v, O (Ŝ⁻v)⟩ = (γ − m² + m) · ⟨v, O v⟩`,   `‖Ŝ⁻v‖² = (γ − m² + m) · ‖v‖²`.

The first is the *cross identity* `su2_expectation_ladder_cross`; the second is the
existing ladder-norm identity (`totalSpinSOpMinus_mulVec_normSq_eq`).  Dividing the
two yields the *real expectation ratio* invariance
`su2_expectationRatioRe_ladder_invariant`: the real Rayleigh quotient
`⟨v, O v⟩.re / ‖v‖²` is unchanged when `v` is lowered by `Ŝ⁻_tot` (when the
lowering is non-vanishing, so `c ≠ 0`).

Derivation of the cross identity, with `⟨a, b⟩ := star a ⬝ᵥ b`:
- `⟨Ŝ⁻v, O Ŝ⁻v⟩ = ⟨v, (Ŝ⁻)ᴴ O Ŝ⁻ v⟩ = ⟨v, Ŝ⁺ O Ŝ⁻ v⟩` since `(Ŝ⁻_tot)ᴴ = Ŝ⁺_tot`
  (`totalSpinSOpMinus_conjTranspose`), using the matrix-adjoint dot-product law
  `star (M *ᵥ a) ⬝ᵥ b = star a ⬝ᵥ (Mᴴ *ᵥ b)` (from `Matrix.star_mulVec` +
  `Matrix.dotProduct_mulVec`).
- `Ŝ⁺ O Ŝ⁻ = O Ŝ⁺ Ŝ⁻` because `O` commutes with `Ŝ⁺_tot`.
- `Ŝ⁺ Ŝ⁻ = (Ŝ_tot)² − (Ŝ³_tot)² + Ŝ³_tot`
  (`totalSpinSOpPlus_mul_totalSpinSOpMinus_eq_casimir_minus_z_sq_add_z`), which acts
  on the joint eigenvector `v` as the scalar `γ − m² + m`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §4 (Theorem 4.4) and §2.5 (Lieb–Mattis / SU(2) ladder structure).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `star v ⬝ᵥ v = ∑ ‖v i‖²` as a real cast into `ℂ`.  Local copy of the (private)
helper `star_dotProduct_self_eq'` of `Theorem23TotalLoweringNonvanishing`, duplicated
here because `private` declarations are not visible across module boundaries. -/
private theorem star_dotProduct_self_eq'' {n : Type*} [Fintype n] (v : n → ℂ) :
    star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  rw [dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]

/-- **Scalar action of `Ŝ⁺_tot Ŝ⁻_tot` on a joint eigenvector.** If
`Ŝ³_tot v = m • v` and `(Ŝ_tot)² v = γ • v`, then
`(Ŝ⁺_tot Ŝ⁻_tot) *ᵥ v = (γ − m·m + m) • v`, the Casimir-rearrangement eigenvalue. -/
theorem totalSpinSOpPlus_mul_totalSpinSOpMinus_mulVec_eq
    {m γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec v = m • v)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v) :
    (totalSpinSOpPlus V N * totalSpinSOpMinus V N).mulVec v =
      (γ - m * m + m) • v := by
  rw [totalSpinSOpPlus_mul_totalSpinSOpMinus_eq_casimir_minus_z_sq_add_z]
  -- `(S² − S³S³ + S³) *ᵥ v`, expand the additive matrix structure.
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, hcas]
  -- `S³S³ *ᵥ v = S³ *ᵥ (S³ *ᵥ v) = m·m • v`.
  rw [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_smul, hz, smul_smul]
  -- now: `γ • v − (m*m) • v + m • v = (γ − m*m + m) • v`.
  module

/-- **SU(2)-invariant expectation cross identity (lowering step).** Let
`O : ManyBodyOpS V N` commute with both total ladder operators
(`hOplus : Commute O Ŝ⁺_tot`, `hOminus : Commute O Ŝ⁻_tot`).  For a joint
`Ŝ³_tot` / Casimir eigenvector `v` (`Ŝ³_tot v = m • v`, `(Ŝ_tot)² v = γ • v`),

  `⟨Ŝ⁻v, O (Ŝ⁻v)⟩ = (γ − m² + m) · ⟨v, O v⟩`,

i.e. the complex expectation of `O` on the once-lowered vector equals the
Casimir-rearrangement scalar `γ − m·m + m` times the expectation on `v`. -/
theorem su2_expectation_ladder_cross (O : ManyBodyOpS V N)
    (hOplus : Commute O (totalSpinSOpPlus V N))
    (_hOminus : Commute O (totalSpinSOpMinus V N))
    {m γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec v = m • v)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v) :
    star ((totalSpinSOpMinus V N).mulVec v) ⬝ᵥ
        (O.mulVec ((totalSpinSOpMinus V N).mulVec v)) =
      (γ - m * m + m) • (star v ⬝ᵥ O.mulVec v) := by
  -- Move `O Ŝ⁻ v` past the adjoint: `⟨Ŝ⁻v, O Ŝ⁻ v⟩ = ⟨v, (Ŝ⁻)ᴴ (O Ŝ⁻ v)⟩`.
  rw [star_mulVec_dotProduct, totalSpinSOpMinus_conjTranspose]
  -- `(Ŝ⁻)ᴴ = Ŝ⁺`; collapse the right-hand vector to the Casimir scalar times `v`:
  -- `Ŝ⁺ *ᵥ (O *ᵥ (Ŝ⁻ *ᵥ v)) = O *ᵥ ((γ − m² + m) • v)`.
  have hcomm : totalSpinSOpPlus V N * O * totalSpinSOpMinus V N =
      O * (totalSpinSOpPlus V N * totalSpinSOpMinus V N) := by
    rw [← hOplus, mul_assoc]
  have hvec : (totalSpinSOpPlus V N).mulVec
      (O.mulVec ((totalSpinSOpMinus V N).mulVec v)) =
      (γ - m * m + m) • O.mulVec v := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm,
      ← Matrix.mulVec_mulVec, totalSpinSOpPlus_mul_totalSpinSOpMinus_mulVec_eq hz hcas,
      Matrix.mulVec_smul]
  rw [hvec, dotProduct_smul, smul_eq_mul]

/-- **SU(2)-invariant real-expectation-ratio ladder invariance.** With the same
SU(2)-invariance and joint-eigenvector hypotheses, if the lowering is non-vanishing
(`Ŝ⁻_tot v ≠ 0`), the real Rayleigh quotient of `O` is preserved by the lowering:

  `⟨Ŝ⁻v, O Ŝ⁻v⟩.re / ⟨Ŝ⁻v, Ŝ⁻v⟩.re = ⟨v, O v⟩.re / ⟨v, v⟩.re`.

Both numerator and denominator scale by the common real factor `(γ − m² + m).re`
(the squared lowering-norm ratio, positive when `Ŝ⁻_tot v ≠ 0`), so the quotient is
unchanged.  Here `⟨a, b⟩ := star a ⬝ᵥ b`. -/
theorem su2_expectationRatioRe_ladder_invariant (O : ManyBodyOpS V N)
    (hOplus : Commute O (totalSpinSOpPlus V N))
    (hOminus : Commute O (totalSpinSOpMinus V N))
    {m γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hz : (totalSpinSOp3 V N).mulVec v = m • v)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v)
    (hne : (totalSpinSOpMinus V N).mulVec v ≠ 0) :
    (star ((totalSpinSOpMinus V N).mulVec v) ⬝ᵥ
          (O.mulVec ((totalSpinSOpMinus V N).mulVec v))).re /
        (star ((totalSpinSOpMinus V N).mulVec v) ⬝ᵥ
          ((totalSpinSOpMinus V N).mulVec v)).re =
      (star v ⬝ᵥ O.mulVec v).re / (star v ⬝ᵥ v).re := by
  set Sm := (totalSpinSOpMinus V N).mulVec v with hSmdef
  -- Numerator scaling: `⟨Ŝ⁻v, O Ŝ⁻v⟩ = (γ − m² + m) • ⟨v, O v⟩`.
  have hnum := su2_expectation_ladder_cross O hOplus hOminus hz hcas
  -- Recast `‖·‖²` casts back into `star · ⬝ᵥ ·` form.
  have hSm_self : star Sm ⬝ᵥ Sm =
      ((∑ i, Complex.normSq (Sm i) : ℝ) : ℂ) := star_dotProduct_self_eq'' Sm
  have hv_self : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) :=
    star_dotProduct_self_eq'' v
  -- The complex scalar factor `c = γ − m² + m`.
  set c : ℂ := γ - m * m + m with hcdef
  -- Denominator scaling rewritten in `star · ⬝ᵥ ·` form.
  have hden : star Sm ⬝ᵥ Sm = c • (star v ⬝ᵥ v) := by
    -- Derive `‖Ŝ⁻v‖² = c·‖v‖²` directly from the cross identity at `O = 1`.
    have hcross1 := su2_expectation_ladder_cross (1 : ManyBodyOpS V N)
      (by simp [Commute.one_left]) (by simp [Commute.one_left]) hz hcas
    simp only [Matrix.one_mulVec] at hcross1
    rw [← hSmdef] at hcross1
    exact hcross1
  -- Numerator scaling in `star · ⬝ᵥ ·` form.
  have hnum' : star Sm ⬝ᵥ (O.mulVec Sm) = c • (star v ⬝ᵥ O.mulVec v) := by
    rw [hSmdef, hcdef]; exact hnum
  -- The denominator real part is non-zero (`‖Ŝ⁻v‖² > 0`).
  have hden_ne : (star Sm ⬝ᵥ Sm).re ≠ 0 := by
    rw [hSm_self, Complex.ofReal_re]
    have hpos : 0 < ∑ i, Complex.normSq (Sm i) := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
        ⟨i, Finset.mem_univ i, lt_of_le_of_ne (Complex.normSq_nonneg _)
          (Ne.symm (by simpa [Complex.normSq_eq_zero] using hi))⟩
    exact ne_of_gt hpos
  -- `c` is real on this eigenvector: from `den` scaling, `c = ‖Ŝ⁻v‖²/‖v‖²` is real.
  -- Extract the real factor `c.re` and `c.im = 0` from the denominator identity.
  have hv_self_re : (star v ⬝ᵥ v).re ≠ 0 := by
    intro h0
    apply hden_ne
    rw [hden]
    -- if `‖v‖² = 0` then `v = 0`, contradicting `Ŝ⁻v ≠ 0`; but easier: re of `c • ‖v‖²`.
    -- `(star v ⬝ᵥ v).re = 0` forces `star v ⬝ᵥ v = 0` (it is a real cast), so `c • 0 = 0`.
    have : star v ⬝ᵥ v = 0 := by
      rw [hv_self] at h0 ⊢; rw [Complex.ofReal_re] at h0; rw [h0]; simp
    rw [this, smul_zero, Complex.zero_re]
  -- `c.im = 0`: both `star Sm ⬝ᵥ Sm` and `star v ⬝ᵥ v` are real casts, so `c` is real.
  have hcim : c.im = 0 := by
    have h1 : (c • (star v ⬝ᵥ v)).im = 0 := by
      rw [← hden, hSm_self, Complex.ofReal_im]
    rw [hv_self, smul_eq_mul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add] at h1
    -- h1 : c.im * (∑ normSq v) = 0; the sum's real cast real part is `(star v ⬝ᵥ v).re ≠ 0`.
    rcases mul_eq_zero.mp h1 with hci | hsum
    · exact hci
    · exfalso; apply hv_self_re; rw [hv_self, Complex.ofReal_re]; exact hsum
  -- Now take real parts of the scalings: `re (c • z) = c.re * z.re` since `c.im = 0`.
  have hnum_re : (star Sm ⬝ᵥ (O.mulVec Sm)).re = c.re * (star v ⬝ᵥ O.mulVec v).re := by
    rw [hnum', smul_eq_mul, Complex.mul_re, hcim, zero_mul, sub_zero]
  have hden_re : (star Sm ⬝ᵥ Sm).re = c.re * (star v ⬝ᵥ v).re := by
    rw [hden, smul_eq_mul, Complex.mul_re, hcim, zero_mul, sub_zero]
  -- `c.re ≠ 0`: else the denominator real part would vanish.
  have hcre_ne : c.re ≠ 0 := by
    intro h0; apply hden_ne; rw [hden_re, h0, zero_mul]
  rw [hnum_re, hden_re, mul_div_mul_left _ _ hcre_ne]

end LatticeSystem.Quantum
