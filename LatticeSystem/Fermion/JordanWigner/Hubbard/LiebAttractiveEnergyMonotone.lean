import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveInteractionIneq

/-!
# The abstract spin-reflection-positivity energy monotonicity (Tasaki §10.2.4)

Thirty-second layer (PR32) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model), in the **corrected Hermitian-`W` endgame**.

Combining the kinetic invariance `|W|² = W²` (PR30) and the interaction inequality
`Re tr(W·I·W·I) ≤ Re tr(|W|·I·|W|·I)` (PR31), the **abstract Lieb energy functional**

  `E(W) = 2·Re tr(W²·T) − 2·Σ_x U_x·Re tr(W·I_x·W·I_x)`  (`U_x ≥ 0`)

is non-increasing under `W ↦ |W|` (the spectral absolute value):

  `E(W) ≥ E(|W|)`.

The kinetic term `2·Re tr(W²·T)` is unchanged (`|W|² = W²`); the attractive
interaction term `−2·Σ_x U_x·Re tr(W·I_x·W·I_x)` (with `U_x ≥ 0`) does not increase,
because each `Re tr(W·I_x·W·I_x) ≤ Re tr(|W|·I_x·|W|·I_x)` and the minus sign with
`U_x ≥ 0` flips the inequality. This is Tasaki eq. (10.2.43), the heart of the
spin-space reflection positivity.

## Main definitions

* `liebSRPEnergy` — the abstract energy functional `E(W)`.

## Main results

* `liebSRPEnergy_abs_le` — `E(|W|) ≤ E(W)` (the SRP energy inequality `E(W) ≥ E(|W|)`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, eq. (10.2.39)/(10.2.43); E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- The abstract Lieb energy functional
`E(W) = 2·Re tr(W²·T) − 2·Σ_x U_x·Re tr(W·I_x·W·I_x)`. -/
noncomputable def liebSRPEnergy (T : Matrix n n ℂ) (Ifn : ι → Matrix n n ℂ)
    (Ufn : ι → ℝ) (W : Matrix n n ℂ) : ℝ :=
  2 * (Matrix.trace (W * W * T)).re
    - 2 * ∑ x : ι, Ufn x * (Matrix.trace (W * Ifn x * W * Ifn x)).re

/-- **The abstract spin-reflection-positivity energy inequality `E(|W|) ≤ E(W)`.**
For Hermitian `W`, Hermitian interaction projections `I_x`, and nonnegative couplings
`U_x ≥ 0`, replacing `W` by its spectral absolute value `|W|` does not increase the
Lieb energy functional. -/
theorem liebSRPEnergy_abs_le {W : Matrix n n ℂ} (hW : W.IsHermitian)
    (T : Matrix n n ℂ) {Ifn : ι → Matrix n n ℂ} (hI : ∀ x, (Ifn x).IsHermitian)
    (Ufn : ι → ℝ) (hU : ∀ x, 0 ≤ Ufn x) :
    liebSRPEnergy T Ifn Ufn (hermitianAbs hW) ≤ liebSRPEnergy T Ifn Ufn W := by
  unfold liebSRPEnergy
  have hkin : Matrix.trace (hermitianAbs hW * hermitianAbs hW * T)
      = Matrix.trace (W * W * T) := by rw [hermitianAbs_mul_self]
  have hsum : ∑ x : ι, Ufn x * (Matrix.trace (W * Ifn x * W * Ifn x)).re
      ≤ ∑ x : ι, Ufn x *
          (Matrix.trace (hermitianAbs hW * Ifn x * hermitianAbs hW * Ifn x)).re :=
    Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (trace_hermitian_interaction_re_le_abs hW (hI x)) (hU x))
  rw [hkin]
  linarith [hsum]

end LatticeSystem.Fermion
