import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal

/-!
# Spin-S operators on `Fin (N + 1)` (Tasaki §2.1, general `S ≥ 0`)

The general spin-`S` Hilbert space `h_0 = ℂ^{2S+1}` is parameterised
here by `N : ℕ` with `2S = N`, so the spin space is `Fin (N + 1)`:

| `N` | `S`   | `dim` |
|-----|-------|-------|
| 0   | 0     | 1     |
| 1   | 1/2   | 2     |
| 2   | 1     | 3     |
| 3   | 3/2   | 4     |
| ... | ...   | ...   |

The basis index `k : Fin (N + 1)` corresponds to the magnetic quantum
number `m_k := S - k = (N : ℝ)/2 - k`, running from `+S` (at `k = 0`)
down to `-S` (at `k = N`).

The standard spin operators are then defined by their action on the
ordered basis `|S, m_0⟩, |S, m_1⟩, …, |S, m_N⟩`:

* `Ŝ^{(3)} |k⟩ = m_k · |k⟩`,
* `Ŝ^+ |k⟩ = √(k · (N − k + 1)) |k − 1⟩` (raises `m`, lowers index),
* `Ŝ^- |k⟩ = √((N − k)(k + 1)) |k + 1⟩`.

This module introduces the matrices `spinSOp3`, `spinSOpPlus`,
`spinSOpMinus` and the linear combinations
`spinSOp1 := (Ŝ^+ + Ŝ^-) / 2` and `spinSOp2 := (Ŝ^+ − Ŝ^-) / (2I)`.

This is the first PR (β-1) of the **Tasaki §2.1 P1d''' track**
(general spin-`S` polynomial decomposition; tracking issue #458).
Subsequent PRs prove the SU(2) commutator algebra (β-2), the
diagonal-projector Lagrange formula (β-3), the off-diagonal
matrix-unit construction (β-4), and the spanning theorem (β-5).

References:

- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.1 Problem 2.1.a (p. 15) and solution S.1
  (p. 493).
- Concrete cases already in the library: `Quantum/SpinHalf.lean`,
  `Quantum/SpinHalfDecomp.lean` (`S = 1/2`, `N = 1`); `Quantum/SpinOne.lean`,
  `Quantum/SpinOneDecomp.lean` (`S = 1`, `N = 2`).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## Diagonal `Ŝ^{(3)}` operator -/

/-- The spin-`S` operator `Ŝ^{(3)}` on the `(N + 1)`-dimensional
spin space, where `N = 2S`.  Diagonal with eigenvalues
`m_k = (N : ℂ)/2 - k` for `k : Fin (N + 1)`. -/
noncomputable def spinSOp3 (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.diagonal fun k : Fin (N + 1) => ((N : ℂ) / 2 - (k.val : ℂ))

/-! ## Raising and lowering operators `Ŝ^±` -/

/-- The spin-`S` raising operator `Ŝ^+`.

Matrix entry `[i, j]` is non-zero iff `i + 1 = j` (raising index by
`-1` corresponds to raising `m` by `+1`); the value is
`√(j · (N − j + 1))`. -/
noncomputable def spinSOpPlus (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j =>
    if i.val + 1 = j.val then
      ((Real.sqrt ((j.val : ℝ) * ((N : ℝ) - (j.val : ℝ) + 1)) : ℝ) : ℂ)
    else 0

/-- The spin-`S` lowering operator `Ŝ^-`.

Matrix entry `[i, j]` is non-zero iff `j + 1 = i` (lowering `m` by
`-1` raises the index by `+1`); the value is
`√((N − j) · (j + 1))`. -/
noncomputable def spinSOpMinus (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j =>
    if j.val + 1 = i.val then
      ((Real.sqrt (((N : ℝ) - (j.val : ℝ)) * ((j.val : ℝ) + 1)) : ℝ) : ℂ)
    else 0

/-! ## Cartesian-axis spin operators `Ŝ^{(1)}`, `Ŝ^{(2)}` -/

/-- The spin-`S` operator `Ŝ^{(1)} = (Ŝ^+ + Ŝ^-) / 2`.  Off-diagonal
real symmetric. -/
noncomputable def spinSOp1 (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  (1 / 2 : ℂ) • (spinSOpPlus N + spinSOpMinus N)

/-- The spin-`S` operator `Ŝ^{(2)} = (Ŝ^+ − Ŝ^-) / (2 i)`.
Off-diagonal pure imaginary anti-symmetric. -/
noncomputable def spinSOp2 (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  (1 / (2 * I) : ℂ) • (spinSOpPlus N - spinSOpMinus N)

/-! ## Basic structural lemmas -/

/-- The diagonal entries of `Ŝ^{(3)}` are exactly the magnetic
quantum numbers `m_k = N/2 − k`. -/
@[simp] theorem spinSOp3_apply_diag (N : ℕ) (k : Fin (N + 1)) :
    spinSOp3 N k k = (N : ℂ) / 2 - (k.val : ℂ) := by
  unfold spinSOp3
  simp [Matrix.diagonal]

/-- Off-diagonal entries of `Ŝ^{(3)}` vanish. -/
@[simp] theorem spinSOp3_apply_offdiag (N : ℕ) {i j : Fin (N + 1)}
    (hij : i ≠ j) : spinSOp3 N i j = 0 := by
  unfold spinSOp3
  rw [Matrix.diagonal_apply_ne _ hij]

/-- The `Ŝ^+` matrix entry on a raising pair. -/
theorem spinSOpPlus_apply_raise (N : ℕ) {i j : Fin (N + 1)}
    (h : i.val + 1 = j.val) :
    spinSOpPlus N i j =
      ((Real.sqrt ((j.val : ℝ) * ((N : ℝ) - (j.val : ℝ) + 1)) : ℝ) : ℂ) := by
  unfold spinSOpPlus
  rw [if_pos h]

/-- Off-raising entries of `Ŝ^+` vanish. -/
theorem spinSOpPlus_apply_other (N : ℕ) {i j : Fin (N + 1)}
    (h : i.val + 1 ≠ j.val) : spinSOpPlus N i j = 0 := by
  unfold spinSOpPlus
  rw [if_neg h]

/-- Diagonal entries of `Ŝ^+` vanish. -/
theorem spinSOpPlus_apply_diag (N : ℕ) (k : Fin (N + 1)) :
    spinSOpPlus N k k = 0 := by
  apply spinSOpPlus_apply_other
  omega

/-- The `Ŝ^-` matrix entry on a lowering pair. -/
theorem spinSOpMinus_apply_lower (N : ℕ) {i j : Fin (N + 1)}
    (h : j.val + 1 = i.val) :
    spinSOpMinus N i j =
      ((Real.sqrt (((N : ℝ) - (j.val : ℝ)) * ((j.val : ℝ) + 1)) : ℝ) : ℂ) := by
  unfold spinSOpMinus
  rw [if_pos h]

/-- Off-lowering entries of `Ŝ^-` vanish. -/
theorem spinSOpMinus_apply_other (N : ℕ) {i j : Fin (N + 1)}
    (h : j.val + 1 ≠ i.val) : spinSOpMinus N i j = 0 := by
  unfold spinSOpMinus
  rw [if_neg h]

/-- Diagonal entries of `Ŝ^-` vanish. -/
theorem spinSOpMinus_apply_diag (N : ℕ) (k : Fin (N + 1)) :
    spinSOpMinus N k k = 0 := by
  apply spinSOpMinus_apply_other
  omega

/-- Diagonal entries of `Ŝ^{(1)}` vanish (it is purely off-diagonal). -/
theorem spinSOp1_apply_diag (N : ℕ) (k : Fin (N + 1)) :
    spinSOp1 N k k = 0 := by
  unfold spinSOp1
  rw [Matrix.smul_apply, Matrix.add_apply,
    spinSOpPlus_apply_diag, spinSOpMinus_apply_diag]
  simp

/-- Diagonal entries of `Ŝ^{(2)}` vanish (it is purely off-diagonal). -/
theorem spinSOp2_apply_diag (N : ℕ) (k : Fin (N + 1)) :
    spinSOp2 N k k = 0 := by
  unfold spinSOp2
  rw [Matrix.smul_apply, Matrix.sub_apply,
    spinSOpPlus_apply_diag, spinSOpMinus_apply_diag]
  simp

/-- Top of the ladder: `Ŝ^+` annihilates the highest-weight state. -/
theorem spinSOpPlus_apply_top (N : ℕ) (j : Fin (N + 1)) :
    spinSOpPlus N (Fin.last N) j = 0 := by
  unfold spinSOpPlus
  rw [if_neg]
  intro h
  -- `(Fin.last N).val + 1 = j.val`, but `j.val ≤ N` so this is impossible.
  have : N + 1 = j.val := by simpa [Fin.val_last] using h
  have : N + 1 ≤ N := this ▸ (Nat.lt_succ_iff.mp j.isLt)
  omega

/-- Bottom of the ladder: `Ŝ^-` annihilates the lowest-weight state. -/
theorem spinSOpMinus_apply_bottom (N : ℕ) (j : Fin (N + 1)) :
    spinSOpMinus N ⟨0, Nat.succ_pos N⟩ j = 0 := by
  unfold spinSOpMinus
  rw [if_neg]
  intro h
  -- `j.val + 1 = (⟨0, _⟩ : Fin (N+1)).val = 0`, impossible.
  simp at h

/-! ## Reduction lemmas to existing concrete cases (sanity checks) -/

/-- For `N = 0` (trivial spin `S = 0`), `Ŝ^{(3)}` is the zero matrix. -/
theorem spinSOp3_zero : spinSOp3 0 = 0 := by
  unfold spinSOp3
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.diagonal]

end LatticeSystem.Quantum
