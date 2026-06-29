import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticW

/-!
# The interaction reconciliation identity `tr(Cᴴ D C (P D P)) = tr(W D W D)` (Tasaki §10.2.4)

Thirty-third layer (PR33b) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model), in the **corrected Hermitian-`W` endgame**.

Companion to the kinetic reconciliation (PR33a). The attractive interaction energy is
the diagonal sandwich `−Σ_x U_x·tr(Cᴴ·D_x·C·E_x)` (PR27), where `D_x` is the up-occupation
diagonal and `E_x` the hole-occupation diagonal. Under the particle-hole **column**
reindex `W := C·P` (`P` a Hermitian involution), the hole diagonal is the particle-hole
conjugate of the occupation diagonal, `E_x = P·D_x·P`, and the interaction trace becomes
a clean form on `W`:

  `tr(Cᴴ·D·C·(P·D·P)) = tr(W·D·W·D)`  (for Hermitian `W = C·P`).

Together with the kinetic identity `tr(Cᴴ(A·C + C·Bᵣ)) = 2·tr(W²·A)` (PR33a), the
half-filled energy is `2·tr(W²·A) − Σ_x U_x·tr(W·D_x·W·D_x)`, matching the abstract
`liebSRPEnergy A D (U/2) W`.

## Main results

* `trace_conj_interaction_eq_trace_W` — `tr(Cᴴ·D·C·(P·D·P)) = tr((C·P)·D·(C·P)·D)` for a
  Hermitian involution `P` and Hermitian `W = C·P`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, eq. (10.2.39); E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The interaction reconciliation identity.** For a Hermitian involution `P`
(`Pᴴ = P`, `P·P = 1`), a diagonal weight `D`, and a coefficient matrix `C` whose
particle-hole reindex `W := C·P` is Hermitian, the diagonal-sandwich interaction trace
`tr(Cᴴ·D·C·(P·D·P))` equals `tr(W·D·W·D)`. -/
theorem trace_conj_interaction_eq_trace_W (C P D : Matrix n n ℂ)
    (hP : P.IsHermitian) (hPinv : P * P = 1) (hW : (C * P).IsHermitian) :
    Matrix.trace (Cᴴ * D * C * (P * D * P))
      = Matrix.trace ((C * P) * D * (C * P) * D) := by
  set W := C * P with hWdef
  have hconj : ∀ X : Matrix n n ℂ, Matrix.trace (P * X * P) = Matrix.trace X := fun X => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPinv, Matrix.one_mul]
  have hC : C = W * P := by rw [hWdef, Matrix.mul_assoc, hPinv, Matrix.mul_one]
  have hCH : Cᴴ = P * W := by
    rw [hC, Matrix.conjTranspose_mul, hW.eq, hP.eq]
  rw [hCH, hC]
  rw [show P * W * D * (W * P) * (P * D * P) = P * W * D * W * (P * P) * D * P from by
      simp only [Matrix.mul_assoc], hPinv, Matrix.mul_one,
    show P * W * D * W * D * P = P * (W * D * W * D) * P from by
      simp only [Matrix.mul_assoc], hconj]

end LatticeSystem.Fermion
