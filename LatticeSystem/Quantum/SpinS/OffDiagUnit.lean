import LatticeSystem.Quantum.SpinS.LadderProj
import Mathlib.Data.Matrix.Basis

/-!
# Off-diagonal matrix-unit decomposition (Tasaki §2.1 P1d''' β-10)

Combining the column-selection lemma (β-6) with the explicit
sub/super-diagonal entries of `Ŝ^±`, we can identify the matrix
products `Ŝ^+ · P_{i+1}` and `Ŝ^- · P_i` with **off-diagonal
matrix units** scaled by the appropriate ladder coefficients:

  `Ŝ^+ · P_{i+1} = √((i + 1)(N − i)) · E_{i, i+1}`,
  `Ŝ^- · P_i     = √((N − i)(i + 1)) · E_{i+1, i}`,

where `E_{a, b} := Matrix.single a b 1` is the (a, b) matrix unit.

These are the simplest off-diagonal matrix units; combined with the
diagonal projectors `P_k` (β-4), the resolution-of-identity (β-9),
and the ladder recursion (β-7), every matrix `M ∈ M_{N + 1}(ℂ)` is
expressible as a polynomial in `{1̂, Ŝ^{(α)}}` (Tasaki Problem 2.1.a),
to be assembled in subsequent PRs.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a (p. 15) and solution S.1 (p. 493).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- `Ŝ^+ · P_{i+1}` equals the off-diagonal matrix unit
`E_{i, i+1}` scaled by the ladder coefficient `√((i+1)(N − i))`. -/
theorem spinSOpPlus_mul_diagProj_succ_eq_single
    (i : Fin (N + 1)) (h : i.val + 1 < N + 1) :
    spinSOpPlus N * spinSDiagProj N ⟨i.val + 1, h⟩ =
      Matrix.single i ⟨i.val + 1, h⟩
        ((Real.sqrt (((i.val : ℝ) + 1) * ((N : ℝ) - (i.val : ℝ))) : ℝ) : ℂ) := by
  ext a b
  rw [spinSOpPlus_mul_diagProj_apply]
  by_cases hb : b = ⟨i.val + 1, h⟩
  · subst hb
    -- (Ŝ^+ * P_{i+1}) at (a, ⟨i+1⟩) = Ŝ^+[a, ⟨i+1⟩]
    rw [if_pos rfl]
    by_cases ha : a = i
    · subst ha
      have hraise : a.val + 1 = (⟨a.val + 1, h⟩ : Fin (N + 1)).val := rfl
      rw [spinSOpPlus_apply_raise N hraise]
      rw [Matrix.single_apply_same]
      push_cast
      congr 2
      ring
    · have hno_raise : ¬ (a.val + 1 = (⟨i.val + 1, h⟩ : Fin (N + 1)).val) := by
        intro heq
        apply ha
        apply Fin.ext
        change a.val = i.val
        change a.val + 1 = i.val + 1 at heq
        omega
      rw [spinSOpPlus_apply_other N hno_raise]
      rw [Matrix.single_apply_of_row_ne (Ne.symm ha) _ _ _]
  · rw [if_neg hb]
    rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hb)]

/-- `Ŝ^- · P_i` equals the off-diagonal matrix unit `E_{i+1, i}`
scaled by the ladder coefficient `√((N − i)(i + 1))`. -/
theorem spinSOpMinus_mul_diagProj_eq_single
    (i : Fin (N + 1)) (h : i.val + 1 < N + 1) :
    spinSOpMinus N * spinSDiagProj N i =
      Matrix.single ⟨i.val + 1, h⟩ i
        ((Real.sqrt (((N : ℝ) - (i.val : ℝ)) * ((i.val : ℝ) + 1)) : ℝ) : ℂ) := by
  ext a b
  rw [spinSOpMinus_mul_diagProj_apply]
  by_cases hb : b = i
  · subst hb
    rw [if_pos rfl]
    by_cases ha : a = ⟨b.val + 1, h⟩
    · subst ha
      have hlower : b.val + 1 = (⟨b.val + 1, h⟩ : Fin (N + 1)).val := rfl
      rw [spinSOpMinus_apply_lower N hlower]
      rw [Matrix.single_apply_same]
    · have hno_lower : ¬ (b.val + 1 = a.val) := by
        intro heq
        apply ha
        apply Fin.ext
        change a.val = b.val + 1
        omega
      rw [spinSOpMinus_apply_other N hno_lower]
      rw [Matrix.single_apply_of_row_ne (Ne.symm ha) _ _ _]
  · rw [if_neg hb]
    rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hb)]

end LatticeSystem.Quantum
