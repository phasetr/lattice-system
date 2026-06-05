import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Matrix.Order

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
open scoped ComplexOrder

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

/-! ### Eigenspace membership of the raised state (full `su(2)`) -/

omit [DecidableEq d] in
/-- `[Ĵ⁽¹⁾, Ĵ⁺] = −Ĵ⁽³⁾`: `Ĵ⁽¹⁾ Ĵ⁺ − Ĵ⁺ Ĵ⁽¹⁾ = −Ĵ⁽³⁾`. -/
private theorem ladderComm1 (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) :
    J1 * (J1 + Complex.I • J2) - (J1 + Complex.I • J2) * J1 = -J3 := by
  have e : J1 * (J1 + Complex.I • J2) - (J1 + Complex.I • J2) * J1
      = Complex.I • (J1 * J2 - J2 * J1) := by
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]; abel
  rw [e, h12, smul_smul, Complex.I_mul_I, neg_one_smul]

omit [DecidableEq d] in
/-- `[Ĵ⁽²⁾, Ĵ⁺] = −i Ĵ⁽³⁾`. -/
private theorem ladderComm2 (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) :
    J2 * (J1 + Complex.I • J2) - (J1 + Complex.I • J2) * J2 = -(Complex.I • J3) := by
  have e : J2 * (J1 + Complex.I • J2) - (J1 + Complex.I • J2) * J2
      = -(J1 * J2 - J2 * J1) := by
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]; abel
  rw [e, h12]

omit [DecidableEq d] in
/-- `[Ĵ⁽³⁾, Ĵ⁺] = Ĵ⁺` (Tasaki eq. (A.3.6)): from `[Ĵ⁽³⁾,Ĵ⁽¹⁾]=iĴ⁽²⁾`, `[Ĵ⁽²⁾,Ĵ⁽³⁾]=iĴ⁽¹⁾`. -/
private theorem ladderComm3 (h23 : J2 * J3 - J3 * J2 = Complex.I • J1)
    (h31 : J3 * J1 - J1 * J3 = Complex.I • J2) :
    J3 * (J1 + Complex.I • J2) - (J1 + Complex.I • J2) * J3 = J1 + Complex.I • J2 := by
  have e : J3 * (J1 + Complex.I • J2) - (J1 + Complex.I • J2) * J3
      = (J3 * J1 - J1 * J3) + Complex.I • (J3 * J2 - J2 * J3) := by
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]; abel
  have h32 : J3 * J2 - J2 * J3 = -(Complex.I • J1) := by rw [← h23]; abel
  rw [e, h31, h32, smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul]; abel

omit [DecidableEq d] in
/-- `[Ĵ², Ĵ⁺] = 0` (Tasaki eq. (A.3.5)): the Casimir commutes with the raising operator. -/
private theorem casimirComm_raise (h12 : J1 * J2 - J2 * J1 = Complex.I • J3)
    (h23 : J2 * J3 - J3 * J2 = Complex.I • J1)
    (h31 : J3 * J1 - J1 * J3 = Complex.I • J2) :
    (J1 * J1 + J2 * J2 + J3 * J3) * (J1 + Complex.I • J2)
      - (J1 + Complex.I • J2) * (J1 * J1 + J2 * J2 + J3 * J3) = 0 := by
  set Jp := J1 + Complex.I • J2 with hJp
  have d1' : J1 * Jp = Jp * J1 + (-J3) := by
    have h := ladderComm1 J1 J2 J3 h12; rw [← hJp] at h
    rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  have d2' : J2 * Jp = Jp * J2 + (-(Complex.I • J3)) := by
    have h := ladderComm2 J1 J2 J3 h12; rw [← hJp] at h
    rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  have d3' : J3 * Jp = Jp * J3 + Jp := by
    have h := ladderComm3 J1 J2 J3 h23 h31; rw [← hJp] at h
    rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  have t1 : J1 * J1 * Jp - Jp * (J1 * J1) = (-J3) * J1 + J1 * (-J3) := by
    calc J1 * J1 * Jp - Jp * (J1 * J1) = J1 * (J1 * Jp) - Jp * J1 * J1 := by noncomm_ring
      _ = J1 * (Jp * J1 + (-J3)) - Jp * J1 * J1 := by rw [d1']
      _ = (J1 * Jp) * J1 + J1 * (-J3) - Jp * J1 * J1 := by noncomm_ring
      _ = (Jp * J1 + (-J3)) * J1 + J1 * (-J3) - Jp * J1 * J1 := by rw [d1']
      _ = (-J3) * J1 + J1 * (-J3) := by noncomm_ring
  have t2 : J2 * J2 * Jp - Jp * (J2 * J2)
      = (-(Complex.I • J3)) * J2 + J2 * (-(Complex.I • J3)) := by
    calc J2 * J2 * Jp - Jp * (J2 * J2) = J2 * (J2 * Jp) - Jp * J2 * J2 := by noncomm_ring
      _ = J2 * (Jp * J2 + (-(Complex.I • J3))) - Jp * J2 * J2 := by rw [d2']
      _ = (J2 * Jp) * J2 + J2 * (-(Complex.I • J3)) - Jp * J2 * J2 := by noncomm_ring
      _ = (Jp * J2 + (-(Complex.I • J3))) * J2 + J2 * (-(Complex.I • J3)) - Jp * J2 * J2 := by
            rw [d2']
      _ = (-(Complex.I • J3)) * J2 + J2 * (-(Complex.I • J3)) := by noncomm_ring
  have t3 : J3 * J3 * Jp - Jp * (J3 * J3) = Jp * J3 + J3 * Jp := by
    calc J3 * J3 * Jp - Jp * (J3 * J3) = J3 * (J3 * Jp) - Jp * J3 * J3 := by noncomm_ring
      _ = J3 * (Jp * J3 + Jp) - Jp * J3 * J3 := by rw [d3']
      _ = (J3 * Jp) * J3 + J3 * Jp - Jp * J3 * J3 := by noncomm_ring
      _ = (Jp * J3 + Jp) * J3 + J3 * Jp - Jp * J3 * J3 := by rw [d3']
      _ = Jp * J3 + J3 * Jp := by noncomm_ring
  have expand : (J1 * J1 + J2 * J2 + J3 * J3) * Jp - Jp * (J1 * J1 + J2 * J2 + J3 * J3)
      = (J1 * J1 * Jp - Jp * (J1 * J1)) + (J2 * J2 * Jp - Jp * (J2 * J2)) +
        (J3 * J3 * Jp - Jp * (J3 * J3)) := by noncomm_ring
  rw [expand, t1, t2, t3, hJp]
  simp only [smul_mul_assoc, mul_smul_comm, neg_mul, mul_neg, mul_add, add_mul]
  abel

omit [DecidableEq d] in
/-- **Tasaki Lemma A.14 (eigenspace membership of the raised state).**  On `H_{J,M}` with the
full `su(2)` relations, the raised state `Ĵ⁺ Φ` lies in `H_{J,M+1}`: it is an `Ĵ²`-eigenvector
at `J(J+1)` (the Casimir is unchanged, since `[Ĵ², Ĵ⁺] = 0`) and an `Ĵ⁽³⁾`-eigenvector at
`M + 1` (since `[Ĵ⁽³⁾, Ĵ⁺] = Ĵ⁺`). -/
theorem angRaise_mem_eigenspace (h12 : J1 * J2 - J2 * J1 = Complex.I • J3)
    (h23 : J2 * J3 - J3 * J2 = Complex.I • J1) (h31 : J3 * J1 - J1 * J3 = Complex.I • J2)
    {Φ : d → ℂ} {Jr M : ℝ}
    (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M : ℂ) • Φ) :
    (J1 * J1 + J2 * J2 + J3 * J3).mulVec ((J1 + Complex.I • J2).mulVec Φ)
        = ((Jr * (Jr + 1) : ℝ) : ℂ) • (J1 + Complex.I • J2).mulVec Φ ∧
      J3.mulVec ((J1 + Complex.I • J2).mulVec Φ)
        = ((M + 1 : ℝ) : ℂ) • (J1 + Complex.I • J2).mulVec Φ := by
  constructor
  · -- `Ĵ² (Ĵ⁺ Φ) = Ĵ⁺ (Ĵ² Φ) = J(J+1) (Ĵ⁺ Φ)` via `[Ĵ², Ĵ⁺] = 0`.
    have hcomm := casimirComm_raise J1 J2 J3 h12 h23 h31
    have : (J1 * J1 + J2 * J2 + J3 * J3).mulVec ((J1 + Complex.I • J2).mulVec Φ)
        = (J1 + Complex.I • J2).mulVec ((J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, sub_eq_zero.mp hcomm]
    rw [this, hsq, Matrix.mulVec_smul]
  · -- `Ĵ⁽³⁾ (Ĵ⁺ Φ) = Ĵ⁺ Ĵ⁽³⁾ Φ + Ĵ⁺ Φ = (M+1) (Ĵ⁺ Φ)` via `[Ĵ⁽³⁾, Ĵ⁺] = Ĵ⁺`.
    have hcomm := ladderComm3 J1 J2 J3 h23 h31
    have key : J3 * (J1 + Complex.I • J2) = (J1 + Complex.I • J2) * J3 + (J1 + Complex.I • J2) := by
      rw [sub_eq_iff_eq_add] at hcomm; rw [hcomm]; abel
    rw [Matrix.mulVec_mulVec, key, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h3,
      Matrix.mulVec_smul]
    push_cast
    module

/-! ### Lowering direction `Ĵ⁻` (mirror of the raising case) -/

/-- `Ĵ⁺ Ĵ⁻ = Ĵ² − Ĵ⁽³⁾(Ĵ⁽³⁾ − 1)` (Tasaki eq. (A.3.8)), from `[Ĵ⁽¹⁾, Ĵ⁽²⁾] = i Ĵ⁽³⁾`. -/
theorem angRaise_mul_angLower (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) :
    (J1 + Complex.I • J2) * (J1 - Complex.I • J2)
      = (J1 * J1 + J2 * J2 + J3 * J3) - J3 * (J3 - 1) := by
  have step : (J1 + Complex.I • J2) * (J1 - Complex.I • J2)
      = J1 * J1 + J2 * J2 - Complex.I • (J1 * J2 - J2 * J1) := by
    simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I,
      neg_smul, one_smul, smul_sub, smul_add]
    abel
  rw [step, h12, smul_smul, Complex.I_mul_I, neg_one_smul]
  noncomm_ring

omit [DecidableEq d] in
/-- **Tasaki Lemma A.14 (lowering, non-vanishing).**  On `H_{J,M}` with `[Ĵ⁽¹⁾,Ĵ⁽²⁾]=iĴ⁽³⁾`, if
`Φ ≠ 0` lies in `H_{J,M}` with `−J < M ≤ J`, then `Ĵ⁻ Φ ≠ 0`.
(`Ĵ⁺ Ĵ⁻ Φ = (J+M)(J−M+1) Φ` with `(J+M)(J−M+1) > 0`.) -/
theorem angLower_mulVec_ne_zero (h12 : J1 * J2 - J2 * J1 = Complex.I • J3)
    {Φ : d → ℂ} {Jr M : ℝ}
    (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M : ℂ) • Φ) (hΦ : Φ ≠ 0) (hlb : -Jr < M) (hub : M ≤ Jr) :
    (J1 - Complex.I • J2).mulVec Φ ≠ 0 := by
  classical
  intro hlow
  have key : ((J1 + Complex.I • J2) * (J1 - Complex.I • J2)).mulVec Φ = 0 := by
    rw [← Matrix.mulVec_mulVec, hlow, Matrix.mulVec_zero]
  rw [angRaise_mul_angLower J1 J2 J3 h12, Matrix.sub_mulVec, hsq] at key
  have h33 : (J3 * (J3 - 1)).mulVec Φ = ((M * (M - 1) : ℝ) : ℂ) • Φ := by
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, h3, Matrix.mulVec_sub,
      Matrix.mulVec_smul, h3]
    push_cast
    module
  rw [h33, ← sub_smul] at key
  have hscalar : ((Jr * (Jr + 1) : ℝ) : ℂ) - ((M * (M - 1) : ℝ) : ℂ)
      = (((Jr + M) * (Jr - M + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [hscalar] at key
  have hpos : (0 : ℝ) < (Jr + M) * (Jr - M + 1) := by apply mul_pos <;> linarith
  rcases smul_eq_zero.mp key with hc | hv
  · exact absurd (Complex.ofReal_eq_zero.mp hc) (ne_of_gt hpos)
  · exact hΦ hv

omit [DecidableEq d] in
/-- `[Ĵ⁽¹⁾, Ĵ⁻] = Ĵ⁽³⁾`. -/
private theorem ladderComm1L (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) :
    J1 * (J1 - Complex.I • J2) - (J1 - Complex.I • J2) * J1 = J3 := by
  have e : J1 * (J1 - Complex.I • J2) - (J1 - Complex.I • J2) * J1
      = -(Complex.I • (J1 * J2 - J2 * J1)) := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]; abel
  rw [e, h12, smul_smul, Complex.I_mul_I, neg_smul, one_smul]; abel

omit [DecidableEq d] in
/-- `[Ĵ⁽²⁾, Ĵ⁻] = −i Ĵ⁽³⁾`. -/
private theorem ladderComm2L (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) :
    J2 * (J1 - Complex.I • J2) - (J1 - Complex.I • J2) * J2 = -(Complex.I • J3) := by
  have e : J2 * (J1 - Complex.I • J2) - (J1 - Complex.I • J2) * J2 = -(J1 * J2 - J2 * J1) := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]; abel
  rw [e, h12]

omit [DecidableEq d] in
/-- `[Ĵ⁽³⁾, Ĵ⁻] = −Ĵ⁻` (Tasaki eq. (A.3.6) lowering). -/
private theorem ladderComm3L (h23 : J2 * J3 - J3 * J2 = Complex.I • J1)
    (h31 : J3 * J1 - J1 * J3 = Complex.I • J2) :
    J3 * (J1 - Complex.I • J2) - (J1 - Complex.I • J2) * J3 = -(J1 - Complex.I • J2) := by
  have e : J3 * (J1 - Complex.I • J2) - (J1 - Complex.I • J2) * J3
      = (J3 * J1 - J1 * J3) - Complex.I • (J3 * J2 - J2 * J3) := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]; abel
  have h32 : J3 * J2 - J2 * J3 = -(Complex.I • J1) := by rw [← h23]; abel
  rw [e, h31, h32, smul_neg, smul_smul, Complex.I_mul_I, neg_smul, one_smul]; abel

omit [DecidableEq d] in
/-- `[Ĵ², Ĵ⁻] = 0` (Tasaki eq. (A.3.5) lowering). -/
private theorem casimirComm_lower (h12 : J1 * J2 - J2 * J1 = Complex.I • J3)
    (h23 : J2 * J3 - J3 * J2 = Complex.I • J1)
    (h31 : J3 * J1 - J1 * J3 = Complex.I • J2) :
    (J1 * J1 + J2 * J2 + J3 * J3) * (J1 - Complex.I • J2)
      - (J1 - Complex.I • J2) * (J1 * J1 + J2 * J2 + J3 * J3) = 0 := by
  set Jm := J1 - Complex.I • J2 with hJm
  have d1' : J1 * Jm = Jm * J1 + J3 := by
    have h := ladderComm1L J1 J2 J3 h12; rw [← hJm] at h
    rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  have d2' : J2 * Jm = Jm * J2 + (-(Complex.I • J3)) := by
    have h := ladderComm2L J1 J2 J3 h12; rw [← hJm] at h
    rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  have d3' : J3 * Jm = Jm * J3 + (-Jm) := by
    have h := ladderComm3L J1 J2 J3 h23 h31; rw [← hJm] at h
    rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  have t1 : J1 * J1 * Jm - Jm * (J1 * J1) = J3 * J1 + J1 * J3 := by
    calc J1 * J1 * Jm - Jm * (J1 * J1) = J1 * (J1 * Jm) - Jm * J1 * J1 := by noncomm_ring
      _ = J1 * (Jm * J1 + J3) - Jm * J1 * J1 := by rw [d1']
      _ = (J1 * Jm) * J1 + J1 * J3 - Jm * J1 * J1 := by noncomm_ring
      _ = (Jm * J1 + J3) * J1 + J1 * J3 - Jm * J1 * J1 := by rw [d1']
      _ = J3 * J1 + J1 * J3 := by noncomm_ring
  have t2 : J2 * J2 * Jm - Jm * (J2 * J2)
      = (-(Complex.I • J3)) * J2 + J2 * (-(Complex.I • J3)) := by
    calc J2 * J2 * Jm - Jm * (J2 * J2) = J2 * (J2 * Jm) - Jm * J2 * J2 := by noncomm_ring
      _ = J2 * (Jm * J2 + (-(Complex.I • J3))) - Jm * J2 * J2 := by rw [d2']
      _ = (J2 * Jm) * J2 + J2 * (-(Complex.I • J3)) - Jm * J2 * J2 := by noncomm_ring
      _ = (Jm * J2 + (-(Complex.I • J3))) * J2 + J2 * (-(Complex.I • J3)) - Jm * J2 * J2 := by
            rw [d2']
      _ = (-(Complex.I • J3)) * J2 + J2 * (-(Complex.I • J3)) := by noncomm_ring
  have t3 : J3 * J3 * Jm - Jm * (J3 * J3) = (-Jm) * J3 + J3 * (-Jm) := by
    calc J3 * J3 * Jm - Jm * (J3 * J3) = J3 * (J3 * Jm) - Jm * J3 * J3 := by noncomm_ring
      _ = J3 * (Jm * J3 + (-Jm)) - Jm * J3 * J3 := by rw [d3']
      _ = (J3 * Jm) * J3 + J3 * (-Jm) - Jm * J3 * J3 := by noncomm_ring
      _ = (Jm * J3 + (-Jm)) * J3 + J3 * (-Jm) - Jm * J3 * J3 := by rw [d3']
      _ = (-Jm) * J3 + J3 * (-Jm) := by noncomm_ring
  have expand : (J1 * J1 + J2 * J2 + J3 * J3) * Jm - Jm * (J1 * J1 + J2 * J2 + J3 * J3)
      = (J1 * J1 * Jm - Jm * (J1 * J1)) + (J2 * J2 * Jm - Jm * (J2 * J2)) +
        (J3 * J3 * Jm - Jm * (J3 * J3)) := by noncomm_ring
  rw [expand, t1, t2, t3, hJm]
  simp only [smul_mul_assoc, mul_smul_comm, neg_mul, mul_neg, mul_sub, sub_mul]
  abel

omit [DecidableEq d] in
/-- **Tasaki Lemma A.14 (eigenspace membership of the lowered state).**  On `H_{J,M}` the
lowered state `Ĵ⁻ Φ` lies in `H_{J,M−1}`: an `Ĵ²`-eigenvector at `J(J+1)` (`[Ĵ²,Ĵ⁻]=0`) and an
`Ĵ⁽³⁾`-eigenvector at `M − 1` (`[Ĵ⁽³⁾,Ĵ⁻]=−Ĵ⁻`). -/
theorem angLower_mem_eigenspace (h12 : J1 * J2 - J2 * J1 = Complex.I • J3)
    (h23 : J2 * J3 - J3 * J2 = Complex.I • J1) (h31 : J3 * J1 - J1 * J3 = Complex.I • J2)
    {Φ : d → ℂ} {Jr M : ℝ}
    (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M : ℂ) • Φ) :
    (J1 * J1 + J2 * J2 + J3 * J3).mulVec ((J1 - Complex.I • J2).mulVec Φ)
        = ((Jr * (Jr + 1) : ℝ) : ℂ) • (J1 - Complex.I • J2).mulVec Φ ∧
      J3.mulVec ((J1 - Complex.I • J2).mulVec Φ)
        = ((M - 1 : ℝ) : ℂ) • (J1 - Complex.I • J2).mulVec Φ := by
  refine ⟨?_, ?_⟩
  · have hcomm := casimirComm_lower J1 J2 J3 h12 h23 h31
    have : (J1 * J1 + J2 * J2 + J3 * J3).mulVec ((J1 - Complex.I • J2).mulVec Φ)
        = (J1 - Complex.I • J2).mulVec ((J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, sub_eq_zero.mp hcomm]
    rw [this, hsq, Matrix.mulVec_smul]
  · have hcomm := ladderComm3L J1 J2 J3 h23 h31
    have key : J3 * (J1 - Complex.I • J2)
        = (J1 - Complex.I • J2) * J3 + (-(J1 - Complex.I • J2)) := by
      rw [sub_eq_iff_eq_add] at hcomm; rw [hcomm]; abel
    rw [Matrix.mulVec_mulVec, key, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h3,
      Matrix.neg_mulVec, Matrix.mulVec_smul]
    push_cast
    module

/-! ### Norm identities (eq. (A.3.9)) and the spin bound `−J ≤ M ≤ J` (Lemma A.15, part 1) -/

omit [Fintype d] [DecidableEq d] in
/-- `(Ĵ⁺)ᴴ = Ĵ⁻` for self-adjoint `Ĵ⁽¹⁾, Ĵ⁽²⁾`. -/
private theorem angRaise_conjTranspose (h1 : J1.IsHermitian) (h2 : J2.IsHermitian) :
    (J1 + Complex.I • J2)ᴴ = J1 - Complex.I • J2 := by
  rw [conjTranspose_add, conjTranspose_smul, h1.eq, h2.eq, Complex.star_def, Complex.conj_I,
    neg_smul]; abel

omit [Fintype d] [DecidableEq d] in
/-- `(Ĵ⁻)ᴴ = Ĵ⁺` for self-adjoint `Ĵ⁽¹⁾, Ĵ⁽²⁾`. -/
private theorem angLower_conjTranspose (h1 : J1.IsHermitian) (h2 : J2.IsHermitian) :
    (J1 - Complex.I • J2)ᴴ = J1 + Complex.I • J2 := by
  rw [conjTranspose_sub, conjTranspose_smul, h1.eq, h2.eq, Complex.star_def, Complex.conj_I,
    neg_smul, sub_neg_eq_add]

omit [DecidableEq d] in
/-- **Tasaki eq. (A.3.9), raising.**  `‖Ĵ⁺ Φ‖² = {J(J+1) − M(M+1)} ‖Φ‖²` on `H_{J,M}`
(self-adjoint `Ĵ⁽¹⁾, Ĵ⁽²⁾`), as a complex identity. -/
theorem angRaise_normSq (h1 : J1.IsHermitian) (h2 : J2.IsHermitian)
    (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) {Φ : d → ℂ} {Jr M : ℝ}
    (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M : ℂ) • Φ) :
    star ((J1 + Complex.I • J2).mulVec Φ) ⬝ᵥ ((J1 + Complex.I • J2).mulVec Φ)
      = ((Jr * (Jr + 1) - M * (M + 1) : ℝ) : ℂ) * (star Φ ⬝ᵥ Φ) := by
  classical
  rw [star_mulVec, ← dotProduct_mulVec, angRaise_conjTranspose J1 J2 h1 h2, Matrix.mulVec_mulVec,
    angLower_mul_angRaise J1 J2 J3 h12]
  have hkey : ((J1 * J1 + J2 * J2 + J3 * J3) - J3 * (J3 + 1)).mulVec Φ
      = ((Jr * (Jr + 1) - M * (M + 1) : ℝ) : ℂ) • Φ := by
    rw [Matrix.sub_mulVec, hsq]
    have h33 : (J3 * (J3 + 1)).mulVec Φ = ((M * (M + 1) : ℝ) : ℂ) • Φ := by
      rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, h3, Matrix.mulVec_add,
        Matrix.mulVec_smul, h3]; push_cast; module
    rw [h33, ← sub_smul]; push_cast; ring_nf
  rw [hkey, dotProduct_smul, smul_eq_mul]

omit [DecidableEq d] in
/-- **Tasaki eq. (A.3.9), lowering.**  `‖Ĵ⁻ Φ‖² = {J(J+1) − M(M−1)} ‖Φ‖²` on `H_{J,M}`. -/
theorem angLower_normSq (h1 : J1.IsHermitian) (h2 : J2.IsHermitian)
    (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) {Φ : d → ℂ} {Jr M : ℝ}
    (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M : ℂ) • Φ) :
    star ((J1 - Complex.I • J2).mulVec Φ) ⬝ᵥ ((J1 - Complex.I • J2).mulVec Φ)
      = ((Jr * (Jr + 1) - M * (M - 1) : ℝ) : ℂ) * (star Φ ⬝ᵥ Φ) := by
  classical
  rw [star_mulVec, ← dotProduct_mulVec, angLower_conjTranspose J1 J2 h1 h2, Matrix.mulVec_mulVec,
    angRaise_mul_angLower J1 J2 J3 h12]
  have hkey : ((J1 * J1 + J2 * J2 + J3 * J3) - J3 * (J3 - 1)).mulVec Φ
      = ((Jr * (Jr + 1) - M * (M - 1) : ℝ) : ℂ) • Φ := by
    rw [Matrix.sub_mulVec, hsq]
    have h33 : (J3 * (J3 - 1)).mulVec Φ = ((M * (M - 1) : ℝ) : ℂ) • Φ := by
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, h3, Matrix.mulVec_sub,
        Matrix.mulVec_smul, h3]; push_cast; module
    rw [h33, ← sub_smul]; push_cast; ring_nf
  rw [hkey, dotProduct_smul, smul_eq_mul]

omit [DecidableEq d] in
/-- **Tasaki Lemma A.15 (the spin bound).**  On a *nonzero* `H_{J,M}` state (self-adjoint
`Ĵ⁽¹⁾, Ĵ⁽²⁾, Ĵ⁽³⁾`, `J ≥ 0`), the magnetic quantum number is bounded: `−J ≤ M ≤ J` (so
`J − M ≥ 0` and `J + M ≥ 0`).  From the nonnegativity of `‖Ĵ⁺ Φ‖²` (eq. (A.3.9)),
`J(J+1) − M(M+1) ≥ 0`, and likewise `J(J+1) − M(M−1) ≥ 0` from `‖Ĵ⁻ Φ‖²`. -/
theorem angMom_abs_le_J (h1 : J1.IsHermitian) (h2 : J2.IsHermitian)
    (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) {Φ : d → ℂ} {Jr M : ℝ} (hΦ : Φ ≠ 0) (hJ : 0 ≤ Jr)
    (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M : ℂ) • Φ) :
    -Jr ≤ M ∧ M ≤ Jr := by
  have hΦpos : (0 : ℂ) < star Φ ⬝ᵥ Φ := Matrix.dotProduct_star_self_pos_iff.mpr hΦ
  have bound : ∀ (Jp : Matrix d d ℂ) (c : ℝ),
      star (Jp.mulVec Φ) ⬝ᵥ (Jp.mulVec Φ) = ((c : ℝ) : ℂ) * (star Φ ⬝ᵥ Φ) → 0 ≤ c := by
    intro Jp c hc
    have hL : (0 : ℂ) ≤ star (Jp.mulVec Φ) ⬝ᵥ (Jp.mulVec Φ) := by
      rcases eq_or_ne (Jp.mulVec Φ) 0 with h0 | h0
      · simp [h0]
      · exact (Matrix.dotProduct_star_self_pos_iff.mpr h0).le
    rw [hc] at hL
    by_contra hneg
    rw [not_le] at hneg
    exact lt_irrefl 0 (lt_of_le_of_lt hL
      (mul_neg_of_neg_of_pos (by exact_mod_cast hneg) hΦpos))
  have hup : 0 ≤ Jr * (Jr + 1) - M * (M + 1) :=
    bound _ _ (angRaise_normSq J1 J2 J3 h1 h2 h12 hsq h3)
  have hlo : 0 ≤ Jr * (Jr + 1) - M * (M - 1) :=
    bound _ _ (angLower_normSq J1 J2 J3 h1 h2 h12 hsq h3)
  constructor <;> nlinarith [hup, hlo]

end LatticeSystem.Math
