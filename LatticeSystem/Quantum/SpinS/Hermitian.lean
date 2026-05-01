/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.Operators
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Hermiticity of the spin-`S` operators (Tasaki §2.1 P1d''' β-3)

The three Cartesian-axis operators `Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}` are
Hermitian for any spin `S`.  The proofs reduce to the **adjointness
of the ladder operators**

  `(Ŝ^+)ᴴ = Ŝ^-`,   `(Ŝ^-)ᴴ = Ŝ^+`.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 (`Ŝ^{(α)}` Hermiticity for any `S`).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

/-! ## Auxiliary scalar identities -/

private lemma star_half_complex : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by simp

private lemma star_one_div_two_mul_I :
    star (1 / (2 * I) : ℂ) = -(1 / (2 * I) : ℂ) := by
  rw [Complex.star_def, map_div₀, map_one, map_mul, map_ofNat, Complex.conj_I]
  field_simp

/-! ## Adjointness of the ladder operators -/

/-- The adjoint of `Ŝ^+` is `Ŝ^-`: `(Ŝ^+)ᴴ = Ŝ^-`. -/
theorem spinSOpPlus_conjTranspose (N : ℕ) :
    (spinSOpPlus N)ᴴ = spinSOpMinus N := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  unfold spinSOpPlus spinSOpMinus
  by_cases h : j.val + 1 = i.val
  · rw [if_pos h, if_pos h, Complex.star_def, Complex.conj_ofReal]
    have hi : (i.val : ℝ) = (j.val : ℝ) + 1 := by exact_mod_cast h.symm
    rw [hi]
    congr 1
    ring
  · rw [if_neg h, if_neg h, Complex.star_def]
    simp

/-- The adjoint of `Ŝ^-` is `Ŝ^+`: `(Ŝ^-)ᴴ = Ŝ^+`. -/
theorem spinSOpMinus_conjTranspose (N : ℕ) :
    (spinSOpMinus N)ᴴ = spinSOpPlus N := by
  rw [← spinSOpPlus_conjTranspose, Matrix.conjTranspose_conjTranspose]

/-! ## Hermiticity of `Ŝ^{(α)}` for `α ∈ {1, 2, 3}` -/

/-- `Ŝ^{(3)}` is Hermitian (real diagonal entries). -/
theorem spinSOp3_isHermitian (N : ℕ) :
    Matrix.IsHermitian (spinSOp3 N) := by
  unfold Matrix.IsHermitian spinSOp3
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases h : i = j
  · subst h
    simp [Matrix.diagonal]
  · have hne : i ≠ j := h
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hne),
        Matrix.diagonal_apply_ne _ hne]
    simp

/-- `Ŝ^{(1)}` is Hermitian: the symmetric combination `(Ŝ^+ + Ŝ^-) / 2`. -/
theorem spinSOp1_isHermitian (N : ℕ) :
    Matrix.IsHermitian (spinSOp1 N) := by
  unfold Matrix.IsHermitian spinSOp1
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      spinSOpPlus_conjTranspose, spinSOpMinus_conjTranspose,
      star_half_complex, add_comm (spinSOpMinus N) (spinSOpPlus N)]

/-- `Ŝ^{(2)}` is Hermitian: the antisymmetric combination
`(Ŝ^+ − Ŝ^-) / (2 i)`. -/
theorem spinSOp2_isHermitian (N : ℕ) :
    Matrix.IsHermitian (spinSOp2 N) := by
  unfold Matrix.IsHermitian spinSOp2
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      spinSOpPlus_conjTranspose, spinSOpMinus_conjTranspose,
      star_one_div_two_mul_I]
  -- Goal: -(1/(2I)) • (Ŝ^- - Ŝ^+) = (1/(2I)) • (Ŝ^+ - Ŝ^-).
  rw [show spinSOpMinus N - spinSOpPlus N = -(spinSOpPlus N - spinSOpMinus N) from
        (neg_sub _ _).symm]
  -- Goal: -(1/(2I)) • -(Ŝ^+ - Ŝ^-) = (1/(2I)) • (Ŝ^+ - Ŝ^-).
  rw [smul_neg, neg_smul]
  abel

end LatticeSystem.Quantum
