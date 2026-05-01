/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.Operators
import Mathlib.Data.Matrix.Diagonal

/-!
# Diagonal projectors and the action of `(Ŝ^{(3)} − λ • 1)`
(Tasaki §2.1 P1d''' β-4)

This module introduces the **diagonal matrix unit** at index `k`,

  `spinSDiagProj N k := diag(δ_{i, k}) = Matrix.diagonal (Pi.single k 1)`,

and proves two key facts that prepare the Lagrange-interpolation
argument for Tasaki Problem 2.1.a:

* **Eigenvalue action**: `(Ŝ^{(3)} − λ_j • 1) · P_k = (λ_k − λ_j) • P_k`,
  where `λ_j := (N : ℂ)/2 − j` is the eigenvalue of `Ŝ^{(3)}` at `j`
  and `P_k := spinSDiagProj N k`.
* **Annihilation**: `(Ŝ^{(3)} − λ_k • 1) · P_k = 0` (the special case
  `j = k`).

These lemmas show that `P_k` is a `(λ_k)`-eigenvector of `Ŝ^{(3)}` and
underpin the Lagrange formula

  `P_k = ∏_{j ≠ k} (Ŝ^{(3)} − λ_j • 1) / (λ_k − λ_j)`,

deferred to a follow-up PR.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a (p. 15) and solution S.1 (p. 493).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-! ## Diagonal projector `P_k = |k⟩⟨k|` -/

/-- The diagonal matrix unit at index `k`: the projector onto the
`k`-th basis vector of the spin-`S` Hilbert space `ℂ^{N+1}`. -/
noncomputable def spinSDiagProj (N : ℕ) (k : Fin (N + 1)) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.diagonal fun i : Fin (N + 1) => if i = k then (1 : ℂ) else 0

/-- The projector is `1` on the diagonal at `k` and `0` elsewhere. -/
@[simp] theorem spinSDiagProj_apply_diag (k : Fin (N + 1)) :
    spinSDiagProj N k k k = 1 := by
  unfold spinSDiagProj
  simp [Matrix.diagonal]

/-- The projector vanishes off the `(k, k)` diagonal. -/
theorem spinSDiagProj_apply_off (k : Fin (N + 1)) {i j : Fin (N + 1)}
    (h : ¬ (i = j ∧ i = k)) :
    spinSDiagProj N k i j = 0 := by
  unfold spinSDiagProj
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    simp [show i ≠ k from fun heq => h ⟨rfl, heq⟩]
  · rw [Matrix.diagonal_apply_ne _ hij]

/-! ## Action of `Ŝ^{(3)} − λ_j • 1` on the projector -/

/-- The shifted operator `Ŝ^{(3)} − λ_j • 1` is itself a diagonal
matrix with entries `λ_i − λ_j = j − i` (in the index variables). -/
theorem spinSOp3_sub_smul_one_eq_diagonal (N : ℕ) (j : Fin (N + 1)) :
    spinSOp3 N - (((N : ℂ) / 2 - (j.val : ℂ)) • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)) =
      Matrix.diagonal fun i : Fin (N + 1) =>
        ((j.val : ℂ) - (i.val : ℂ)) := by
  ext i j'
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  unfold spinSOp3
  by_cases h : i = j'
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    simp
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
    simp [if_neg h]

/-- **Eigenvalue action**: the shifted operator `Ŝ^{(3)} − λ_j • 1`
acts on the `k`-th projector by the scalar `λ_k − λ_j`:

`(Ŝ^{(3)} − λ_j • 1) · P_k = (λ_k − λ_j) · P_k = (j − k) · P_k`. -/
theorem spinSOp3_sub_smul_mul_diagProj (N : ℕ) (k j : Fin (N + 1)) :
    (spinSOp3 N - (((N : ℂ) / 2 - (j.val : ℂ)) •
        (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℂ))) *
      spinSDiagProj N k =
      ((j.val : ℂ) - (k.val : ℂ)) • spinSDiagProj N k := by
  rw [spinSOp3_sub_smul_one_eq_diagonal]
  unfold spinSDiagProj
  rw [Matrix.diagonal_mul_diagonal]
  ext i j'
  rw [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hij : i = j'
  · subst hij
    by_cases h : i = k
    · subst h; simp
    · simp [if_neg h]
  · simp [if_neg hij]

/-- **Annihilation**: the shifted operator at `j = k` annihilates
`P_k`: `(Ŝ^{(3)} − λ_k • 1) · P_k = 0`. -/
theorem spinSOp3_sub_smul_self_mul_diagProj (N : ℕ) (k : Fin (N + 1)) :
    (spinSOp3 N - (((N : ℂ) / 2 - (k.val : ℂ)) •
        (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℂ))) *
      spinSDiagProj N k = 0 := by
  rw [spinSOp3_sub_smul_mul_diagProj]
  simp

end LatticeSystem.Quantum
