import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Tasaki Appendix A.3: the angular-momentum ladder (Lemma A.14)

The abstract angular-momentum operators `Ĵ⁽¹⁾, Ĵ⁽²⁾, Ĵ⁽³⁾` satisfy the `su(2)` commutation
relations `[Ĵ⁽ᵅ⁾, Ĵ⁽ᵝ⁾] = i ε_{αβγ} Ĵ⁽ᵞ⁾` (eq. (A.3.1)).  With `Ĵ² = (Ĵ⁽¹⁾)² + (Ĵ⁽²⁾)² +
(Ĵ⁽³⁾)²` and the ladder operators `Ĵ± = Ĵ⁽¹⁾ ± i Ĵ⁽²⁾`, one has the key operator identity
`Ĵ⁻ Ĵ⁺ = Ĵ² − Ĵ⁽³⁾(Ĵ⁽³⁾ + 1)` (eq. (A.3.7)).

**Lemma A.14** (the raising/lowering ladder): on the joint eigenspace `H_{J,M}`
(`Ĵ² Φ = J(J+1) Φ`, `Ĵ⁽³⁾ Φ = M Φ`), if `Φ ≠ 0` and `M < J` (within the physical range
`−J ≤ M`), then `Ĵ⁺ Φ ≠ 0` and `Ĵ⁺ Φ ∈ H_{J,M+1}`.  Tasaki's `‖Ĵ⁺ Φ‖² =
{J(J+1) − M(M+1)} ‖Φ‖²` (eq. (A.3.9)); the non-vanishing follows already at the operator
level (`Ĵ⁻ Ĵ⁺ Φ = {J(J+1) − M(M+1)} Φ`), and `J(J+1) − M(M+1) = (J−M)(J+M+1) > 0`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.3, eqs. (A.3.1)–(A.3.9), Lemma A.14, pp. 471–472.
-/

namespace LatticeSystem.Math

open Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]
  (J1 J2 J3 : Matrix d d ℂ)

/-- `Ĵ⁻ Ĵ⁺ = Ĵ² − Ĵ⁽³⁾(Ĵ⁽³⁾ + 1)` (Tasaki eq. (A.3.7)), from `[Ĵ⁽¹⁾, Ĵ⁽²⁾] = i Ĵ⁽³⁾`. -/
theorem angLower_mul_angRaise (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) :
    (J1 - Complex.I • J2) * (J1 + Complex.I • J2)
      = (J1 * J1 + J2 * J2 + J3 * J3) - J3 * (J3 + 1) := by
  have step : (J1 - Complex.I • J2) * (J1 + Complex.I • J2)
      = J1 * J1 + J2 * J2 + Complex.I • (J1 * J2 - J2 * J1) := by
    simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I,
      neg_smul, one_smul, smul_sub]
    abel
  rw [step, h12, smul_smul, Complex.I_mul_I, neg_one_smul]
  noncomm_ring

omit [DecidableEq d] in
/-- **Tasaki Lemma A.14 (angular-momentum ladder, non-vanishing).**  On `H_{J,M}` with the
`su(2)` relation `[Ĵ⁽¹⁾, Ĵ⁽²⁾] = i Ĵ⁽³⁾`, if `Φ ≠ 0` lies in the joint eigenspace
(`Ĵ² Φ = J(J+1) Φ`, `Ĵ⁽³⁾ Φ = M Φ`) with `−J ≤ M < J` (the physical range), then the raised
state `Ĵ⁺ Φ` is nonzero.  (`Ĵ⁻ Ĵ⁺ Φ = (J−M)(J+M+1) Φ` with `(J−M)(J+M+1) > 0`.) -/
theorem angRaise_mulVec_ne_zero (h12 : J1 * J2 - J2 * J1 = Complex.I • J3)
    {Φ : d → ℂ} {Jr M : ℝ}
    (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M : ℂ) • Φ) (hΦ : Φ ≠ 0) (hlb : -Jr ≤ M) (hub : M < Jr) :
    (J1 + Complex.I • J2).mulVec Φ ≠ 0 := by
  classical
  intro hraise
  -- `Ĵ⁻ Ĵ⁺ Φ = 0`, but also `= (J(J+1) − M(M+1)) Φ`, a nonzero scalar times a nonzero vector.
  have key : ((J1 - Complex.I • J2) * (J1 + Complex.I • J2)).mulVec Φ = 0 := by
    rw [← Matrix.mulVec_mulVec, hraise, Matrix.mulVec_zero]
  rw [angLower_mul_angRaise J1 J2 J3 h12, Matrix.sub_mulVec, hsq] at key
  -- `Ĵ⁽³⁾(Ĵ⁽³⁾+1) Φ = M(M+1) Φ`
  have h33 : (J3 * (J3 + 1)).mulVec Φ = ((M * (M + 1) : ℝ) : ℂ) • Φ := by
    rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, h3, Matrix.mulVec_add,
      Matrix.mulVec_smul, h3]
    push_cast
    module
  rw [h33, ← sub_smul] at key
  have hscalar : ((Jr * (Jr + 1) : ℝ) : ℂ) - ((M * (M + 1) : ℝ) : ℂ)
      = (((Jr - M) * (Jr + M + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [hscalar] at key
  have hpos : (0 : ℝ) < (Jr - M) * (Jr + M + 1) := by
    apply mul_pos
    · linarith
    · linarith
  rcases smul_eq_zero.mp key with hc | hv
  · exact absurd (Complex.ofReal_eq_zero.mp hc) (ne_of_gt hpos)
  · exact hΦ hv

end LatticeSystem.Math
