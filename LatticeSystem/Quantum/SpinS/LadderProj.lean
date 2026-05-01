import LatticeSystem.Quantum.SpinS.DiagProj

/-!
# Ladder action `Ŝ^± · P_k` of the spin-`S` raising/lowering operators
on diagonal projectors (Tasaki §2.1 P1d''' β-6)

The diagonal projector `P_k = spinSDiagProj N k` interacts with the
raising and lowering operators as follows:

* **Right multiplication** by `P_k` "selects column `k`": for any
  matrix `A`, `(A · P_k)[i, j] = A[i, k]` if `j = k`, else `0`.
* **Left multiplication** by `P_k` "selects row `k`": dually,
  `(P_k · A)[i, j] = A[k, j]` if `i = k`, else `0`.

Specialised to `A = Ŝ^±` and combined with the sub/super-diagonal
structure of `Ŝ^±`, these select **off-diagonal matrix units** —
the basic building blocks for the polynomial decomposition of
`M_{N+1}(ℂ)` (Tasaki Problem 2.1.a, S.1):

* `Ŝ^+ · P_k = √(k · (N − k + 1)) · E_{k−1, k}` for `k ≥ 1`,
* `P_k · Ŝ^+ = √((k+1) · (N − k)) · E_{k, k+1}` for `k ≤ N − 1`.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a (p. 15) and solution S.1 (p. 493).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-! ## Right/left multiplication by `P_k` selects a column / row -/

/-- For any matrix `A` over `Fin (N + 1)`, right-multiplication by
the diagonal projector `P_k = spinSDiagProj N k` zeroes out every
column except column `k`:

`(A · P_k)[i, j] = A[i, k]` if `j = k`, otherwise `0`. -/
theorem mul_diagProj_apply (k : Fin (N + 1))
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (i j : Fin (N + 1)) :
    (A * spinSDiagProj N k) i j = if j = k then A i k else 0 := by
  rw [Matrix.mul_apply]
  unfold spinSDiagProj
  by_cases h : j = k
  · subst h
    rw [if_pos rfl]
    -- Goal: ∑ l, A i l * (diagonal (fun i' => if i' = j then 1 else 0)) l j = A i j
    rw [Finset.sum_eq_single j]
    · rw [Matrix.diagonal_apply_eq, if_pos rfl, mul_one]
    · intros l _ hlj
      rw [Matrix.diagonal_apply_ne _ hlj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hlj : l = j
    · subst hlj
      rw [Matrix.diagonal_apply_eq, if_neg h, mul_zero]
    · rw [Matrix.diagonal_apply_ne _ hlj, mul_zero]

/-- Dual: left-multiplication by `P_k` zeroes out every row except
row `k`:

`(P_k · A)[i, j] = A[k, j]` if `i = k`, otherwise `0`. -/
theorem diagProj_mul_apply (k : Fin (N + 1))
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (i j : Fin (N + 1)) :
    (spinSDiagProj N k * A) i j = if i = k then A k j else 0 := by
  rw [Matrix.mul_apply]
  unfold spinSDiagProj
  by_cases h : i = k
  · subst h
    rw [if_pos rfl]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq, if_pos rfl, one_mul]
    · intros l _ hli
      rw [Matrix.diagonal_apply_ne' _ hli, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hli : l = i
    · subst hli
      rw [Matrix.diagonal_apply_eq, if_neg h, zero_mul]
    · rw [Matrix.diagonal_apply_ne' _ hli, zero_mul]

/-! ## Specialisation to `Ŝ^+` and `Ŝ^-` -/

/-- The matrix entry `(Ŝ^+ · P_k)[i, j]` is non-zero exactly at the
single position `(k − 1, k)` (for `k ≥ 1`); the value is the
ladder coefficient `√(k · (N − k + 1))`. -/
theorem spinSOpPlus_mul_diagProj_apply (k : Fin (N + 1)) (i j : Fin (N + 1)) :
    (spinSOpPlus N * spinSDiagProj N k) i j =
      if j = k then spinSOpPlus N i k else 0 :=
  mul_diagProj_apply k (spinSOpPlus N) i j

/-- The matrix entry `(Ŝ^- · P_k)[i, j]` is non-zero exactly at the
single position `(k + 1, k)` (for `k ≤ N − 1`); the value is the
ladder coefficient `√((N − k) · (k + 1))`. -/
theorem spinSOpMinus_mul_diagProj_apply (k : Fin (N + 1)) (i j : Fin (N + 1)) :
    (spinSOpMinus N * spinSDiagProj N k) i j =
      if j = k then spinSOpMinus N i k else 0 :=
  mul_diagProj_apply k (spinSOpMinus N) i j

end LatticeSystem.Quantum
