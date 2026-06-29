import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveEnergyTrace
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The attractive interaction energy as a diagonal-sandwich trace form (Tasaki §10.2.1)

Twenty-seventh layer (PR27) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

PR24/PR26 expressed the attractive interaction energy as a diagonal `normSq` sum
`Σ_{u,h} (Σ_x −U_x u_x (1−h_x)) |C_{u,h}|²`. This file rewrites that sum as a
**trace form** sandwiching the coefficient matrix between site-occupation diagonals:

  `= −Σ_x U_x · tr(Cᴴ · D_x · C · E_x)`,

where `D_x = diag(u ↦ u_x)` is the up-occupation diagonal and `E_x = diag(h ↦ 1−h_x)`
is the hole-occupation diagonal. Both are positive-semidefinite (their entries are
`0` or `1`). This is the form on which the spin-reflection variational replacement
`C ↦ |C| = (CᴴC)^{1/2}` acts, via the Lieb trace inequality
`tr(Cᴴ D C E) ≤ tr(|C| D |C| E)` (a later layer): with `−U_x ≤ 0`, replacing `C` by
`|C|` does not raise the interaction energy.

## Main definitions

* `hubbardUpOccupationDiag` / `hubbardHoleOccupationDiag` — the site-occupation
  diagonals `D_x`, `E_x` (positive-semidefinite).

## Main results

* `trace_conjTranspose_mul_diagonal_mul_diagonal_eq_sum_normSq` — the generic
  diagonal-sandwich trace expansion `tr(Cᴴ (D C E)) = Σ_{i,j} d_i e_j |C_{i,j}|²`.
* `attractiveInteraction_normSq_sum_eq_trace_form` — the interaction diagonal `normSq`
  sum as the diagonal-sandwich trace form.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Complex
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- The up-occupation diagonal matrix `D_x = diag(u ↦ u_x)` at site `x`. -/
noncomputable def hubbardUpOccupationDiag (N : ℕ) (x : Fin (N + 1)) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  Matrix.diagonal fun u => ((u x).val : ℂ)

/-- The hole-occupation diagonal matrix `E_x = diag(h ↦ 1 − h_x)` at site `x`. -/
noncomputable def hubbardHoleOccupationDiag (N : ℕ) (x : Fin (N + 1)) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  Matrix.diagonal fun h => (1 - ((h x).val : ℂ))

/-- The up-occupation diagonal is positive-semidefinite (entries `0` or `1`). -/
theorem hubbardUpOccupationDiag_posSemidef (N : ℕ) (x : Fin (N + 1)) :
    (hubbardUpOccupationDiag N x).PosSemidef := by
  unfold hubbardUpOccupationDiag
  refine Matrix.PosSemidef.diagonal ?_
  intro u
  rcases show u x = 0 ∨ u x = 1 from by omega with h | h
  · simp [h]
  · simp [h, zero_le_one]

/-- The hole-occupation diagonal is positive-semidefinite (entries `0` or `1`). -/
theorem hubbardHoleOccupationDiag_posSemidef (N : ℕ) (x : Fin (N + 1)) :
    (hubbardHoleOccupationDiag N x).PosSemidef := by
  unfold hubbardHoleOccupationDiag
  refine Matrix.PosSemidef.diagonal ?_
  intro hc
  rcases show hc x = 0 ∨ hc x = 1 from by omega with h | h
  · simp [h, zero_le_one]
  · simp [h]

/-- The diagonal-sandwich trace expansion: `tr(Cᴴ · diag d · C · diag e)` is the
weighted sum of the squared magnitudes `Σ_{i,j} d_i e_j |C_{i,j}|²`. -/
theorem trace_conjTranspose_mul_diagonal_mul_diagonal_eq_sum_normSq {ι : Type*}
    [Fintype ι] [DecidableEq ι] (C : Matrix ι ι ℂ) (d e : ι → ℂ) :
    Matrix.trace (Cᴴ * (Matrix.diagonal d * C * Matrix.diagonal e))
      = ∑ i : ι, ∑ j : ι, d i * e j * (Complex.normSq (C i j) : ℂ) := by
  rw [trace_conjTranspose_mul_eq_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
    show (Complex.normSq (C i j) : ℂ) = star (C i j) * C i j from by
      rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]]
  ring

/-- **The attractive interaction diagonal `normSq` sum as a diagonal-sandwich trace
form** `−Σ_x U_x · tr(Cᴴ · D_x · C · E_x)`. -/
theorem attractiveInteraction_normSq_sum_eq_trace_form (N : ℕ)
    (U : Fin (N + 1) → ℝ)
    (C : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    (∑ u : hubbardSpinConfig N, ∑ h : hubbardSpinConfig N,
        ((∑ x : Fin (N + 1), -U x * ((u x).val : ℝ) * (1 - ((h x).val : ℝ)) : ℝ) : ℂ) *
          (Complex.normSq (C u h) : ℂ))
      = ∑ x : Fin (N + 1), -(U x : ℂ) *
          Matrix.trace
            (Cᴴ * (hubbardUpOccupationDiag N x * C * hubbardHoleOccupationDiag N x)) := by
  have hrhs : (∑ x : Fin (N + 1), -(U x : ℂ) *
      Matrix.trace
        (Cᴴ * (hubbardUpOccupationDiag N x * C * hubbardHoleOccupationDiag N x)))
      = ∑ x : Fin (N + 1), ∑ u : hubbardSpinConfig N, ∑ h : hubbardSpinConfig N,
          -(U x : ℂ) * (((u x).val : ℂ) * (1 - ((h x).val : ℂ)) *
            (Complex.normSq (C u h) : ℂ)) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hubbardUpOccupationDiag, hubbardHoleOccupationDiag,
      trace_conjTranspose_mul_diagonal_mul_diagonal_eq_sum_normSq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum]
  rw [hrhs]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  ring

end LatticeSystem.Fermion
