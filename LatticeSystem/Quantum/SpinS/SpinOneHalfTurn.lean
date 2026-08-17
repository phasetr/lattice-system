import LatticeSystem.Quantum.SpinOneBasis
import LatticeSystem.Quantum.SpinS.Hermitian
import LatticeSystem.Quantum.SpinS.SpinSReversal

/-!
# The spin-one per-site half turns `u_α = exp(i π Ŝ^{(α)})`

For `S = 1` the operator `Ŝ^{(α)}` has eigenvalues `{1, 0, -1}`, so `(Ŝ^{(α)})³ = Ŝ^{(α)}` and the
`π` rotation about axis `α` has the polynomial closed form

  `exp(i π Ŝ^{(α)}) = 1 - 2 (Ŝ^{(α)})²`.

The three matrices themselves are the existing `spinOnePiRot1`, `spinOnePiRot2`, `spinOnePiRot3` of
`Quantum/SpinOneBasis.lean`; this module packages them as one family indexed by `alpha : Fin 3` and
supplies the algebraic identities used by the §8.1.3 edge-state analysis: the polynomial
characterisation, involutivity, self-adjointness, the conjugation law `u_α Ŝ^{(β)} u_α = ± Ŝ^{(β)}`
(`+` exactly when `α = β`), and stability of the family under conjugation by any of its members.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.1, eqs. (2.1.21), (2.1.23) and (2.1.29)–(2.1.30), pp. 17–19; §8.1.3, footnote 11, p. 237
(the `S = 1` restriction is essential for the closed form).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The single-site **spin-one axis operator** `Ŝ^{(α)}` selected by `α : Fin 3`
(`0 ↦ Ŝ^{(1)}`, `1 ↦ Ŝ^{(2)}`, `2 ↦ Ŝ^{(3)}`).  This is the single-site companion of the
many-body selector `spinSSiteComponentS`.

**Declared overlap.**  This is definitionally `spinSOpFin3 2` of `RingReflectionRingInstance`.  The
overlap is deliberate: `spinSOpFin3` lives in the Theorem 4.2 reflection-positivity layer, so
reusing it would pull roughly 44 extra modules into the import closure of this low-level module in
exchange for a purely definitional convenience. -/
noncomputable def spinOneAxisS (alpha : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![spinSOp1 2, spinSOp2 2, spinSOp3 2] alpha

/-- Every spin-one axis operator is Hermitian. -/
theorem spinOneAxisS_isHermitian (alpha : Fin 3) : (spinOneAxisS alpha).IsHermitian := by
  fin_cases alpha
  · exact spinSOp1_isHermitian 2
  · exact spinSOp2_isHermitian 2
  · exact spinSOp3_isHermitian 2

/-- The **per-site spin-one half turn** `u_α = exp(i π Ŝ^{(α)}) = 1 - 2 (Ŝ^{(α)})²`, the closed
form valid because `(Ŝ^{(α)})³ = Ŝ^{(α)}` at `S = 1` (Tasaki (2.1.21)/(2.1.23), pp. 17–18;
footnote 11, p. 237, records that the `S = 1` restriction is essential).

The members are literally the existing π-rotation matrices `spinOnePiRot1`, `spinOnePiRot2`,
`spinOnePiRot3` of `Quantum/SpinOneBasis.lean`: this definition only turns those three constants
into the `Fin 3`-indexed family that the axis-symmetric §8.1.3 argument quantifies over.  The
polynomial form is recovered by `spinOneHalfTurnS_eq_one_sub_two_smul_sq`.  No Lean bridge to
`NormedSpace.exp` is attempted: it is off the critical path, and the repository already lets a
concrete phase and an `exp` form coexist without a proved bridge (`AKLTStringOrderDefs`).

**Declared overlap.**  At `alpha = 2` the value equals the single constant
`spinSStringPhaseS1 = diagonal (k ↦ (-1)^(k+1)) = diag(-1, 1, -1)` of `AKLTStringOrderDefs`.  That
§7.2 constant is left untouched so that already-discharged material is not disturbed. -/
def spinOneHalfTurnS (alpha : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![spinOnePiRot1, spinOnePiRot2, spinOnePiRot3] alpha

/-- `(√2)² = 2` as a complex scalar; the single irrational entry appearing in the explicit
spin-one matrices. -/
private theorem sqrtTwo_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- At `S = 1` the generic raising operator is the explicit constant `spinOneOpPlus` of
`Quantum/SpinOneBasis.lean`. -/
private theorem spinSOpPlus_two_eq : spinSOpPlus 2 = spinOneOpPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinSOpPlus, spinOneOpPlus]

/-- At `S = 1` the generic lowering operator is the explicit constant `spinOneOpMinus` of
`Quantum/SpinOneBasis.lean`. -/
private theorem spinSOpMinus_two_eq : spinSOpMinus 2 = spinOneOpMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [spinSOpMinus, spinOneOpMinus]

/-- **The half turn is the `S = 1` polynomial in its axis operator**: `u_α = 1 - 2 (Ŝ^{(α)})²`
(Tasaki, the unnumbered display `e^{-iπŜ^{(α)}} = 1̂ - 2 (Ŝ^{(α)})²` introducing (2.1.33), p. 20).
This is the bridge between the explicit matrices `spinOnePiRot1/2/3` that define the family and the
operator identities proved from the polynomial form.

**Declared overlap.**  This is a near-restatement of `spinOnePiRot1_eq`, `spinOnePiRot2_eq` and
`spinOnePiRot3_eq` of `Quantum/SpinOneBasis.lean`, which prove the same three identities with the
axis operator written as `spinOneOp1/2/3`, whereas the §8.1.3 argument needs the `spinSOp1/2/3 2`
representation packaged by `spinOneAxisS`.  The near-twin is necessary rather than deliberate: the
repository has no bridging lemma `spinOneOpα = spinSOpα 2`, so neither form is obtainable from the
other by rewriting. -/
theorem spinOneHalfTurnS_eq_one_sub_two_smul_sq (alpha : Fin 3) :
    spinOneHalfTurnS alpha = 1 - (2 : ℂ) • (spinOneAxisS alpha) ^ 2 := by
  fin_cases alpha
  · change spinOnePiRot1 = 1 - (2 : ℂ) • (spinOneAxisS 0) ^ 2
    have h1 : spinOneAxisS 0 = (1 / 2 : ℂ) • (spinSOpPlus 2 + spinSOpMinus 2) := rfl
    rw [h1, spinSOpPlus_two_eq, spinSOpMinus_two_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, spinOnePiRot1, spinOneOpPlus, spinOneOpMinus] <;> ring_nf <;>
        simp [sqrtTwo_sq] <;> norm_num
  · change spinOnePiRot2 = 1 - (2 : ℂ) • (spinOneAxisS 1) ^ 2
    have h2 : spinOneAxisS 1 = (1 / (2 * Complex.I) : ℂ) • (spinSOpPlus 2 - spinSOpMinus 2) := rfl
    rw [h2, spinSOpPlus_two_eq, spinSOpMinus_two_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, spinOnePiRot2, spinOneOpPlus, spinOneOpMinus] <;> ring_nf <;>
        simp [Complex.I_sq, sqrtTwo_sq] <;> norm_num
  · change spinOnePiRot3 = 1 - (2 : ℂ) • (spinOneAxisS 2) ^ 2
    have h3 : spinOneAxisS 2 = spinSOp3 2 := rfl
    rw [h3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, spinSOp3, spinOnePiRot3] <;> norm_num

/-- The **axis-1 half turn is the negated single-site reversal**: `u_1 = -F`.  Hence conjugation by
`u_1` agrees with conjugation by `F`, whose full action on `Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}` is already
available. -/
theorem spinOneHalfTurnS_zero_eq : spinOneHalfTurnS 0 = -spinReversalS 2 := by
  change spinOnePiRot1 = -spinReversalS 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinOnePiRot1, spinReversalS, Fin.rev]

/-- The **axis-3 half turn is the diagonal π-rotation matrix** `spinOnePiRot3 = diag(-1, 1, -1)`. -/
theorem spinOneHalfTurnS_two_eq : spinOneHalfTurnS 2 = spinOnePiRot3 := rfl

/-- The **axis-2 half turn is the product of the other two**, `u_2 = u_1 u_3`, matching the
spin-`S` relation `û_1 û_2 = û_3` with no extra phase (Tasaki (2.1.29)–(2.1.30), p. 19). -/
theorem spinOneHalfTurnS_one_eq :
    spinOneHalfTurnS 1 = spinOneHalfTurnS 0 * spinOneHalfTurnS 2 := by
  change spinOnePiRot2 = spinOnePiRot1 * spinOnePiRot3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinOnePiRot1, spinOnePiRot2, spinOnePiRot3, Matrix.mul_apply, Fin.sum_univ_three]

/-- **The half turn commutes with its own axis operator**: `u_α Ŝ^{(α)} = Ŝ^{(α)} u_α`, both being
polynomials in `Ŝ^{(α)}`.  This is the crux of the mutual commutativity of the string terms
`A_x = Ŝ_x^{(α)} R^{(α)}_{<x}` in the §8.1.3 support argument. -/
theorem spinOneHalfTurnS_commute_spinOneAxisS (alpha : Fin 3) :
    Commute (spinOneHalfTurnS alpha) (spinOneAxisS alpha) := by
  change spinOneHalfTurnS alpha * spinOneAxisS alpha = spinOneAxisS alpha * spinOneHalfTurnS alpha
  rw [spinOneHalfTurnS_eq_one_sub_two_smul_sq, Matrix.sub_mul, Matrix.mul_sub, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, pow_two, mul_assoc]

/-- The axis-1 and axis-3 half turns commute (the integer-spin commutation
`spinOnePiRot3_comm_spinOnePiRot1`). -/
private theorem spinOneHalfTurnS_zero_mul_two_comm :
    spinOneHalfTurnS 0 * spinOneHalfTurnS 2 = spinOneHalfTurnS 2 * spinOneHalfTurnS 0 :=
  spinOnePiRot3_comm_spinOnePiRot1.symm

/-- Conjugation by the axis-2 half turn factors as conjugation by the axis-3 half turn followed by
conjugation by the axis-1 half turn, since `u_2 = u_1 u_3` and `u_1`, `u_3` commute. -/
private theorem spinOneHalfTurnS_one_conj (X : Matrix (Fin 3) (Fin 3) ℂ) :
    spinOneHalfTurnS 1 * X * spinOneHalfTurnS 1 =
      spinOneHalfTurnS 0 * (spinOneHalfTurnS 2 * X * spinOneHalfTurnS 2) * spinOneHalfTurnS 0 := by
  rw [spinOneHalfTurnS_one_eq]
  nth_rewrite 2 [spinOneHalfTurnS_zero_mul_two_comm]
  noncomm_ring

/-- **Each half turn is an involution**: `u_α² = 1` (the `S = 1` form of `(û_α)² = Û_{2π} = 1`,
Tasaki (2.1.23), p. 17; the three instances are `spinOnePiRot{1,2,3}_sq`). -/
theorem spinOneHalfTurnS_mul_self (alpha : Fin 3) :
    spinOneHalfTurnS alpha * spinOneHalfTurnS alpha = 1 := by
  fin_cases alpha
  · exact spinOnePiRot1_sq
  · exact spinOnePiRot2_sq
  · exact spinOnePiRot3_sq

/-- **Each half turn is self-adjoint**: `u_αᴴ = u_α`, since `Ŝ^{(α)}` is Hermitian and `u_α` is a
real polynomial in it.  This is what makes each string term `Ŝ_x^{(α)} R^{(α)}_{<x}` Hermitian
(Tasaki p. 236: `(e^{iπŜ})† = e^{-iπŜ} = e^{iπŜ}` at `S = 1`). -/
theorem spinOneHalfTurnS_isHermitian (alpha : Fin 3) : (spinOneHalfTurnS alpha).IsHermitian := by
  have hS := (spinOneAxisS_isHermitian alpha).eq
  change (spinOneHalfTurnS alpha)ᴴ = spinOneHalfTurnS alpha
  rw [spinOneHalfTurnS_eq_one_sub_two_smul_sq, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, pow_two, Matrix.conjTranspose_mul, hS]
  norm_num [pow_two]

/-- Conjugating an axis operator by **its own** half turn is trivial. -/
private theorem spinOneHalfTurnS_conj_self (alpha : Fin 3) :
    spinOneHalfTurnS alpha * spinOneAxisS alpha * spinOneHalfTurnS alpha =
      spinOneAxisS alpha := by
  rw [(spinOneHalfTurnS_commute_spinOneAxisS alpha).eq, mul_assoc,
    spinOneHalfTurnS_mul_self alpha, mul_one]

/-- Conjugating the raising operator by the axis-3 half turn flips its sign. -/
private theorem spinOneHalfTurnS_two_conj_spinSOpPlus :
    spinOneHalfTurnS 2 * spinSOpPlus 2 * spinOneHalfTurnS 2 = -spinSOpPlus 2 := by
  rw [spinOneHalfTurnS_two_eq, spinSOpPlus_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, spinOnePiRot3, spinOneOpPlus]

/-- Conjugating the lowering operator by the axis-3 half turn flips its sign. -/
private theorem spinOneHalfTurnS_two_conj_spinSOpMinus :
    spinOneHalfTurnS 2 * spinSOpMinus 2 * spinOneHalfTurnS 2 = -spinSOpMinus 2 := by
  rw [spinOneHalfTurnS_two_eq, spinSOpMinus_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, spinOnePiRot3, spinOneOpMinus]

/-- Axis-3 half turn versus the axis-1 spin component: `u_3 Ŝ^{(1)} u_3 = -Ŝ^{(1)}`. -/
private theorem spinOneHalfTurnS_two_conj_axis_zero :
    spinOneHalfTurnS 2 * spinOneAxisS 0 * spinOneHalfTurnS 2 = (-1 : ℂ) • spinOneAxisS 0 := by
  have h : spinOneAxisS 0 = (1 / 2 : ℂ) • (spinSOpPlus 2 + spinSOpMinus 2) := rfl
  rw [h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    spinOneHalfTurnS_two_conj_spinSOpPlus, spinOneHalfTurnS_two_conj_spinSOpMinus]
  module

/-- Axis-3 half turn versus the axis-2 spin component: `u_3 Ŝ^{(2)} u_3 = -Ŝ^{(2)}`. -/
private theorem spinOneHalfTurnS_two_conj_axis_one :
    spinOneHalfTurnS 2 * spinOneAxisS 1 * spinOneHalfTurnS 2 = (-1 : ℂ) • spinOneAxisS 1 := by
  have h : spinOneAxisS 1 = (1 / (2 * Complex.I) : ℂ) • (spinSOpPlus 2 - spinSOpMinus 2) := rfl
  rw [h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    spinOneHalfTurnS_two_conj_spinSOpPlus, spinOneHalfTurnS_two_conj_spinSOpMinus]
  module

/-- Axis-1 half turn versus the axis-2 spin component: `u_1 Ŝ^{(2)} u_1 = -Ŝ^{(2)}`. -/
private theorem spinOneHalfTurnS_zero_conj_axis_one :
    spinOneHalfTurnS 0 * spinOneAxisS 1 * spinOneHalfTurnS 0 = (-1 : ℂ) • spinOneAxisS 1 := by
  have h : spinOneAxisS 1 = spinSOp2 2 := rfl
  rw [h, spinOneHalfTurnS_zero_eq]
  simp only [neg_mul, mul_neg]
  rw [spinReversalS_conj_spinSOp2]
  module

/-- Axis-1 half turn versus the axis-3 spin component: `u_1 Ŝ^{(3)} u_1 = -Ŝ^{(3)}`. -/
private theorem spinOneHalfTurnS_zero_conj_axis_two :
    spinOneHalfTurnS 0 * spinOneAxisS 2 * spinOneHalfTurnS 0 = (-1 : ℂ) • spinOneAxisS 2 := by
  have h : spinOneAxisS 2 = spinSOp3 2 := rfl
  rw [h, spinOneHalfTurnS_zero_eq]
  simp only [neg_mul, mul_neg]
  rw [spinReversalS_conj_spinSOp3]
  module

/-- Axis-2 half turn versus the axis-1 spin component: `u_2 Ŝ^{(1)} u_2 = -Ŝ^{(1)}`. -/
private theorem spinOneHalfTurnS_one_conj_axis_zero :
    spinOneHalfTurnS 1 * spinOneAxisS 0 * spinOneHalfTurnS 1 = (-1 : ℂ) • spinOneAxisS 0 := by
  rw [spinOneHalfTurnS_one_conj, spinOneHalfTurnS_two_conj_axis_zero, Matrix.mul_smul,
    Matrix.smul_mul, spinOneHalfTurnS_conj_self]

/-- Axis-2 half turn versus the axis-3 spin component: `u_2 Ŝ^{(3)} u_2 = -Ŝ^{(3)}`. -/
private theorem spinOneHalfTurnS_one_conj_axis_two :
    spinOneHalfTurnS 1 * spinOneAxisS 2 * spinOneHalfTurnS 1 = (-1 : ℂ) • spinOneAxisS 2 := by
  rw [spinOneHalfTurnS_one_conj, spinOneHalfTurnS_conj_self,
    spinOneHalfTurnS_zero_conj_axis_two]

/-- Off-diagonal half-turn conjugation: `u_α Ŝ^{(β)} u_α = -Ŝ^{(β)}` whenever `α ≠ β`. -/
private theorem spinOneHalfTurnS_conj_spinOneAxisS_of_ne {alpha beta : Fin 3}
    (hab : alpha ≠ beta) :
    spinOneHalfTurnS alpha * spinOneAxisS beta * spinOneHalfTurnS alpha =
      (-1 : ℂ) • spinOneAxisS beta := by
  fin_cases alpha <;> fin_cases beta
  · exact absurd rfl hab
  · exact spinOneHalfTurnS_zero_conj_axis_one
  · exact spinOneHalfTurnS_zero_conj_axis_two
  · exact spinOneHalfTurnS_one_conj_axis_zero
  · exact absurd rfl hab
  · exact spinOneHalfTurnS_one_conj_axis_two
  · exact spinOneHalfTurnS_two_conj_axis_zero
  · exact spinOneHalfTurnS_two_conj_axis_one
  · exact absurd rfl hab

/-- **The half-turn conjugation law** `u_α Ŝ^{(β)} u_α = ± Ŝ^{(β)}`, with the `+` sign exactly when
`α = β` (Tasaki (2.1.16), p. 16; the `θ = π` form is (2.1.21), p. 17).  This is the source of the
character table (8.1.12), p. 238. -/
theorem spinOneHalfTurnS_conj_spinOneAxisS (alpha beta : Fin 3) :
    spinOneHalfTurnS alpha * spinOneAxisS beta * spinOneHalfTurnS alpha =
      (if alpha = beta then (1 : ℂ) else -1) • spinOneAxisS beta := by
  by_cases h : alpha = beta
  · subst h
    rw [if_pos rfl, one_smul]
    exact spinOneHalfTurnS_conj_self alpha
  · rw [if_neg h]
    exact spinOneHalfTurnS_conj_spinOneAxisS_of_ne h

/-- **The half-turn family is stable under its own conjugation**: `u_α u_β u_α = u_β`.  Immediate
from the conjugation law, because the sign is squared away by `(Ŝ^{(β)})²`. -/
theorem spinOneHalfTurnS_conj_spinOneHalfTurnS (alpha beta : Fin 3) :
    spinOneHalfTurnS alpha * spinOneHalfTurnS beta * spinOneHalfTurnS alpha =
      spinOneHalfTurnS beta := by
  have hinv := spinOneHalfTurnS_mul_self alpha
  have hconj := spinOneHalfTurnS_conj_spinOneAxisS alpha beta
  have hbeta : spinOneHalfTurnS beta
      = 1 - (2 : ℂ) • (spinOneAxisS beta * spinOneAxisS beta) := by
    rw [spinOneHalfTurnS_eq_one_sub_two_smul_sq, pow_two]
  have hsq : spinOneHalfTurnS alpha * (spinOneAxisS beta * spinOneAxisS beta)
        * spinOneHalfTurnS alpha
      = (spinOneHalfTurnS alpha * spinOneAxisS beta * spinOneHalfTurnS alpha) *
        (spinOneHalfTurnS alpha * spinOneAxisS beta * spinOneHalfTurnS alpha) := by
    calc spinOneHalfTurnS alpha * (spinOneAxisS beta * spinOneAxisS beta)
            * spinOneHalfTurnS alpha
        = spinOneHalfTurnS alpha * spinOneAxisS beta
            * (spinOneHalfTurnS alpha * spinOneHalfTurnS alpha)
            * spinOneAxisS beta * spinOneHalfTurnS alpha := by rw [hinv]; noncomm_ring
      _ = _ := by noncomm_ring
  have hsign : ((if alpha = beta then (1 : ℂ) else -1) • spinOneAxisS beta) *
      ((if alpha = beta then (1 : ℂ) else -1) • spinOneAxisS beta)
      = spinOneAxisS beta * spinOneAxisS beta := by
    by_cases h : alpha = beta
    · rw [if_pos h, one_smul]
    · rw [if_neg h, neg_smul, one_smul, neg_mul_neg]
  rw [hbeta, Matrix.mul_sub, Matrix.sub_mul, mul_one, hinv, Matrix.mul_smul, Matrix.smul_mul,
    hsq, hconj, hsign]

end LatticeSystem.Quantum
