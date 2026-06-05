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

end LatticeSystem.Math
