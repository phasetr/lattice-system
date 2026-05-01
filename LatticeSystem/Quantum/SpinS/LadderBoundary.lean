import LatticeSystem.Quantum.SpinS.LadderProj

/-!
# Ladder boundary annihilation: `Ŝ^+ · P_0 = 0` and `Ŝ^- · P_N = 0`
(Tasaki §2.1 P1d''' β-8)

The raising operator annihilates the highest-weight projector
(top of ladder), and the lowering operator annihilates the
lowest-weight projector (bottom of ladder).  Equivalently, the
**columns** of `Ŝ^±` at the corresponding extreme indices vanish:

* `(Ŝ^+)[i, 0] = 0` for all `i` (no `i + 1 = 0`),
* `(Ŝ^-)[i, N] = 0` for all `i` (no `j + 1 = i` with `j = N`).

Combined with the column-selection lemma (β-6, `mul_diagProj_apply`),
these give the matrix products `Ŝ^+ · P_0 = 0` and `Ŝ^- · P_N = 0`.

These are the **boundary conditions** for the ladder recursion
(β-7), terminating the iteration at the highest- and lowest-weight
projectors.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a (p. 15) and solution S.1 (p. 493).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-! ## Column-zero lemmas for the ladder operators -/

/-- The first column of `Ŝ^+` is zero: `(Ŝ^+)[i, ⟨0, _⟩] = 0` for all
`i`.  Equivalently, `Ŝ^+` cannot raise from below the highest weight.
-/
theorem spinSOpPlus_apply_first_col (i : Fin (N + 1)) :
    spinSOpPlus N i ⟨0, Nat.succ_pos N⟩ = 0 := by
  unfold spinSOpPlus
  rw [if_neg]
  intro h
  -- `i.val + 1 = 0`, impossible.
  simp at h

/-- The last column of `Ŝ^-` is zero: `(Ŝ^-)[i, Fin.last N] = 0` for
all `i`.  Equivalently, `Ŝ^-` cannot lower from above the lowest
weight. -/
theorem spinSOpMinus_apply_last_col (i : Fin (N + 1)) :
    spinSOpMinus N i (Fin.last N) = 0 := by
  unfold spinSOpMinus
  rw [if_neg]
  intro h
  -- `(Fin.last N).val + 1 = i.val`, but `i.val ≤ N`.
  have : N + 1 = i.val := by simpa [Fin.val_last] using h
  have : N + 1 ≤ N := this ▸ (Nat.lt_succ_iff.mp i.isLt)
  omega

/-! ## Ladder boundary annihilation `Ŝ^± · P_{0/N} = 0` -/

/-- **Top of ladder**: `Ŝ^+ · P_0 = 0`.  The first column of
`Ŝ^+` is zero, so right-multiplication by `P_0` (which selects
column `0`) yields the zero matrix. -/
theorem spinSOpPlus_mul_diagProj_first :
    spinSOpPlus N * spinSDiagProj N ⟨0, Nat.succ_pos N⟩ = 0 := by
  ext i j
  rw [spinSOpPlus_mul_diagProj_apply]
  by_cases h : j = ⟨0, Nat.succ_pos N⟩
  · rw [if_pos h, spinSOpPlus_apply_first_col]
    rfl
  · rw [if_neg h]
    rfl

/-- **Bottom of ladder**: `Ŝ^- · P_N = 0`.  The last column of
`Ŝ^-` is zero, so right-multiplication by `P_N` (which selects
column `N`) yields the zero matrix. -/
theorem spinSOpMinus_mul_diagProj_last :
    spinSOpMinus N * spinSDiagProj N (Fin.last N) = 0 := by
  ext i j
  rw [spinSOpMinus_mul_diagProj_apply]
  by_cases h : j = Fin.last N
  · rw [if_pos h, spinSOpMinus_apply_last_col]
    rfl
  · rw [if_neg h]
    rfl

end LatticeSystem.Quantum
