import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic

/-!
# The kinetic reconciliation identity `tr(Cᴴ(AC + C Bᵣ)) = 2 tr(W²A)` (Tasaki §10.2.4)

Thirty-third layer (PR33a) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model), in the **corrected Hermitian-`W` endgame**.

The remaining endgame expresses the half-filled attractive-Hubbard energy as the
abstract Lieb energy functional `liebSRPEnergy` on a **Hermitian** coefficient matrix
`W`. The correct `W` is the block coefficient matrix `C` with a particle-hole **column**
reindex, `W := C · P` (`P = particle-hole permutation matrix`, a Hermitian involution),
so that the block kinetic action `C ↦ A·C + C·Bᵣ` (with `Bᵣ = P·Aᴴ·P`, PR22) becomes a
clean quadratic form on `W`:

  `tr(Cᴴ·(A·C + C·(P·Aᴴ·P))) = 2·tr(W²·A)`  (for Hermitian `W = C·P`, Hermitian `A`).

This file proves that purely matrix-algebraic identity (cyclic trace + `P² = 1`); the
Hubbard specialization (`A = hubbardBlockKineticUpFixedMatrix`, the sector, the full
energy) is a subsequent layer.

## Main results

* `trace_conj_kinetic_eq_two_trace_W_sq` — `tr(Cᴴ(AC + C(P Aᴴ P))) = 2 tr((CP)²A)` for a
  Hermitian involution `P`, Hermitian `A`, and Hermitian `W = C·P`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, eq. (10.2.39); E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The kinetic reconciliation identity.** For a Hermitian involution `P`
(`Pᴴ = P`, `P·P = 1`), a Hermitian `A`, and a coefficient matrix `C` whose
particle-hole reindex `W := C·P` is Hermitian, the block kinetic quadratic form
`tr(Cᴴ·(A·C + C·(P·Aᴴ·P)))` equals `2·tr(W²·A)`. -/
theorem trace_conj_kinetic_eq_two_trace_W_sq (A C P : Matrix n n ℂ)
    (hA : A.IsHermitian) (hP : P.IsHermitian) (hPinv : P * P = 1)
    (hW : (C * P).IsHermitian) :
    Matrix.trace (Cᴴ * (A * C + C * (P * Aᴴ * P)))
      = 2 * Matrix.trace ((C * P) * (C * P) * A) := by
  set W := C * P with hWdef
  -- `tr(P·X·P) = tr(X)` for the involution `P`.
  have hconj : ∀ X : Matrix n n ℂ, Matrix.trace (P * X * P) = Matrix.trace X := fun X => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPinv, Matrix.one_mul]
  have hC : C = W * P := by rw [hWdef, Matrix.mul_assoc, hPinv, Matrix.mul_one]
  have hCH : Cᴴ = P * W := by
    rw [hC, Matrix.conjTranspose_mul, hW.eq, hP.eq]
  rw [hCH, hC, hA.eq, Matrix.mul_add, Matrix.trace_add, two_mul]
  congr 1
  · -- `tr(P W (A (W P))) = tr(W W A)`
    rw [show P * W * (A * (W * P)) = P * (W * A * W) * P from by
      simp only [Matrix.mul_assoc], hconj]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  · -- `tr(P W ((W P)(P A P))) = tr(W W A)`
    rw [show P * W * (W * P * (P * A * P)) = P * (W * W * (P * P) * A) * P from by
      simp only [Matrix.mul_assoc], hPinv, Matrix.mul_one, hconj]

end LatticeSystem.Fermion
