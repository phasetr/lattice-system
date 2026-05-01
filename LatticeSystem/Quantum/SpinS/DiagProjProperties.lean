import LatticeSystem.Quantum.SpinS.DiagProj
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Properties of the spin-`S` diagonal projector
(Tasaki §2.1 P1d''' β-9)

Two fundamental linear-algebra facts about the diagonal projectors
`P_k = spinSDiagProj N k`:

* **Hermiticity**: each `P_k` is Hermitian (its diagonal entries
  `δ_{i, k}` are real).
* **Resolution of the identity**: the projectors sum to the
  identity matrix, `Σ_k P_k = 1`.

The resolution-of-identity equation is the cornerstone of the
matrix-unit decomposition of `M_{N + 1}(ℂ)`: combining `1 = Σ_k P_k`
with the ladder construction of off-diagonal matrix units (via
`Ŝ^±` ladder action on each `P_k`, β-6 / β-7) gives every matrix
unit and hence every matrix in `M_{N + 1}(ℂ)`.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a (p. 15) and solution S.1 (p. 493).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-! ## Hermiticity -/

/-- Each diagonal projector `P_k = spinSDiagProj N k` is Hermitian
(real diagonal). -/
theorem spinSDiagProj_isHermitian (k : Fin (N + 1)) :
    Matrix.IsHermitian (spinSDiagProj N k) := by
  unfold Matrix.IsHermitian spinSDiagProj
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases h : i = j
  · subst h
    simp [Matrix.diagonal]
  · have hne : i ≠ j := h
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hne),
        Matrix.diagonal_apply_ne _ hne]
    simp

/-! ## Resolution of the identity -/

/-- **Resolution of the identity**: the diagonal projectors `P_k`
for `k : Fin (N + 1)` sum to the identity matrix:

`Σ_k P_k = 1`. -/
theorem sum_spinSDiagProj_eq_one :
    ∑ k : Fin (N + 1), spinSDiagProj N k =
      (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) := by
  ext i j
  rw [Matrix.one_apply, Matrix.sum_apply]
  unfold spinSDiagProj
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
      simp
    · intros k _ hki
      rw [Matrix.diagonal_apply_eq]
      rw [if_neg (Ne.symm hki)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.diagonal_apply_ne _ h]

end LatticeSystem.Quantum
