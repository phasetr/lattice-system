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
* `frobenius_conj_isometry` — the Frobenius norm-square sum is invariant under isometry
  conjugation `A ↦ J·A·Jᴴ` (`Jᴴ·J = 1`).
* `liebSRPEnergy_conj_isometry` — the Lieb energy functional of the conjugated matrix
  `J·A·Jᴴ` equals that of `A` for the conjugated kinetic/interaction data.

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

/-- **The Frobenius norm-square sum is invariant under isometry conjugation.**
For an isometry `J` (`Jᴴ·J = 1`) and any `A`, the sum of squared magnitudes of the
conjugated matrix `J·A·Jᴴ` equals that of `A`. Both sides equal `tr(Aᴴ·A)`. -/
theorem frobenius_conj_isometry {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    {J : Matrix n m ℂ} (hJ : Jᴴ * J = 1) (A : Matrix m m ℂ) :
    ∑ u : n, ∑ v : n, (Complex.normSq ((J * A * Jᴴ) u v) : ℂ)
      = ∑ s : m, ∑ t : m, (Complex.normSq (A s t) : ℂ) := by
  have hn : ∑ u : n, ∑ v : n, (Complex.normSq ((J * A * Jᴴ) u v) : ℂ)
      = Matrix.trace ((J * A * Jᴴ)ᴴ * (J * A * Jᴴ)) := by
    rw [trace_conjTranspose_mul_eq_sum]
    exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => by
      rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]))
  have hm : ∑ s : m, ∑ t : m, (Complex.normSq (A s t) : ℂ) = Matrix.trace (Aᴴ * A) := by
    rw [trace_conjTranspose_mul_eq_sum]
    exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => by
      rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]))
  have hMM : (J * A * Jᴴ)ᴴ * (J * A * Jᴴ) = J * (Aᴴ * A) * Jᴴ := by
    rw [show (J * A * Jᴴ)ᴴ = J * Aᴴ * Jᴴ from by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
            Matrix.mul_assoc]]
    rw [show J * Aᴴ * Jᴴ * (J * A * Jᴴ) = J * Aᴴ * (Jᴴ * J) * A * Jᴴ from by
          simp only [Matrix.mul_assoc], hJ, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [hn, hm, hMM, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

/-- **The Lieb energy functional under isometry conjugation.**
For an isometry `J` (`Jᴴ·J = 1`), the energy `E` of the conjugated coefficient matrix
`J·A·Jᴴ` (with full-space kinetic `T` and interaction projections `Ifn`) equals the
energy of `A` computed with the compressed kinetic `Jᴴ·T·J` and interaction
`x ↦ Jᴴ·(Ifn x)·J`. Both terms transport by trace cyclicity and `Jᴴ·J = 1`. -/
theorem liebSRPEnergy_conj_isometry {n m : Type*} [Fintype n] [Fintype m]
    [DecidableEq m] {J : Matrix n m ℂ} (hJ : Jᴴ * J = 1) (T : Matrix n n ℂ)
    (Ifn : ι → Matrix n n ℂ) (Ufn : ι → ℝ) (A : Matrix m m ℂ) :
    liebSRPEnergy T Ifn Ufn (J * A * Jᴴ)
      = liebSRPEnergy (Jᴴ * T * J) (fun x => Jᴴ * Ifn x * J) Ufn A := by
  have hkin : Matrix.trace ((J * A * Jᴴ) * (J * A * Jᴴ) * T)
      = Matrix.trace (A * A * (Jᴴ * T * J)) := by
    rw [show (J * A * Jᴴ) * (J * A * Jᴴ) * T = J * (A * (Jᴴ * J) * A * Jᴴ * T) from by
          simp only [Matrix.mul_assoc], hJ, Matrix.mul_one, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hint : ∀ I : Matrix n n ℂ,
      Matrix.trace ((J * A * Jᴴ) * I * (J * A * Jᴴ) * I)
        = Matrix.trace (A * (Jᴴ * I * J) * A * (Jᴴ * I * J)) := fun I => by
    rw [show (J * A * Jᴴ) * I * (J * A * Jᴴ) * I = J * (A * Jᴴ * I * J * A * Jᴴ * I) from by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hsum : ∑ x : ι, Ufn x
        * (Matrix.trace ((J * A * Jᴴ) * Ifn x * (J * A * Jᴴ) * Ifn x)).re
      = ∑ x : ι, Ufn x * (Matrix.trace (A * (Jᴴ * Ifn x * J) * A * (Jᴴ * Ifn x * J))).re :=
    Finset.sum_congr rfl (fun x _ => by rw [hint (Ifn x)])
  simp only [liebSRPEnergy]
  rw [hkin, hsum]

end LatticeSystem.Fermion
