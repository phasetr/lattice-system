/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.DiagProj

/-!
# Idempotence and orthogonality of the spin-`S` diagonal projectors
(Tasaki §2.1 P1d''' β-23)

The diagonal projectors `P_k = |k⟩⟨k|` (β-4) form a **complete
orthogonal family** on the spin-`S` Hilbert space `ℂ^{N+1}`:

* `P_k · P_k = P_k` (idempotence),
* `P_i · P_j = 0` for `i ≠ j` (orthogonality).

Combined with β-9 (`∑_k P_k = 1`, resolution of identity) this gives
the **spectral decomposition of `1̂`** for the diagonal observable
`Ŝ^{(3)}`.

Both proofs reduce immediately to the diagonal-matrix calculus
`Matrix.diagonal_mul_diagonal`.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {N : ℕ}

/-- **Idempotence**: `P_k · P_k = P_k`. -/
theorem spinSDiagProj_mul_self (N : ℕ) (k : Fin (N + 1)) :
    spinSDiagProj N k * spinSDiagProj N k = spinSDiagProj N k := by
  unfold spinSDiagProj
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  by_cases h : i = k
  · simp [h]
  · simp [h]

/-- **Orthogonality**: `P_i · P_j = 0` whenever `i ≠ j`. -/
theorem spinSDiagProj_mul_of_ne (N : ℕ) {i j : Fin (N + 1)} (h : i ≠ j) :
    spinSDiagProj N i * spinSDiagProj N j = 0 := by
  unfold spinSDiagProj
  rw [Matrix.diagonal_mul_diagonal]
  ext a b
  rw [Matrix.diagonal_apply, Matrix.zero_apply]
  by_cases hab : a = b
  · simp only [if_pos hab]
    by_cases hai : a = i
    · subst hai
      simp [show ¬ a = j from fun heq => h (heq ▸ hab.symm ▸ rfl)]
    · simp [hai]
  · simp [hab]

end LatticeSystem.Quantum
