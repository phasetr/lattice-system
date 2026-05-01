/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.OffDiagUnit
import LatticeSystem.Quantum.SpinS.ProjMemAdjoin
import LatticeSystem.Quantum.SpinS.PMMemAdjoin

/-!
# Immediate-neighbor matrix units live in `Algebra.adjoin ℂ {Ŝ^{(α)}}`
(Tasaki §2.1 P1d''' β-29)

The matrix units `E_{i, i+1}` and `E_{i+1, i}` (i.e., the upper- and
lower-immediate-neighbor matrix units) are members of the unital
`ℂ`-subalgebra of `Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ` generated
by the spin operators:

  `Matrix.single i ⟨i+1, h⟩ 1 ∈ Algebra.adjoin ℂ {Ŝ^{(α)}}`,
  `Matrix.single ⟨i+1, h⟩ i 1 ∈ Algebra.adjoin ℂ {Ŝ^{(α)}}`.

Proof: β-10 gives `Ŝ^+ · P_{i+1} = √((i+1)(N-i)) · E_{i, i+1}`
(and similarly for `Ŝ^-`). Both `Ŝ^+, Ŝ^-` (β-28) and `P_k`
(β-27) are in the adjoin; subalgebras are closed under
multiplication and scalar `smul`. The ladder coefficient
`√((i+1)(N-i))` is non-zero on the valid range `i.val + 1 ≤ N`.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- The ladder coefficient is positive on the valid range. -/
private theorem ladder_coeff_pos {N : ℕ} (i : Fin (N + 1))
    (h : i.val + 1 < N + 1) :
    0 < Real.sqrt (((i.val : ℝ) + 1) * ((N : ℝ) - (i.val : ℝ))) := by
  apply Real.sqrt_pos.mpr
  apply mul_pos
  · positivity
  · have : i.val + 1 ≤ N := by omega
    have : (i.val : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast this
    linarith

/-- The matrix unit `E_{i, i+1} ∈ Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`. -/
theorem single_succ_mem_adjoin (i : Fin (N + 1)) (h : i.val + 1 < N + 1) :
    Matrix.single i (⟨i.val + 1, h⟩ : Fin (N + 1)) (1 : ℂ) ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) := by
  set c : ℝ :=
    Real.sqrt (((i.val : ℝ) + 1) * ((N : ℝ) - (i.val : ℝ)))
  have hc_pos : 0 < c := ladder_coeff_pos i h
  have hc_ne : (c : ℂ) ≠ 0 := by
    intro hzero
    have : (c : ℝ) = 0 := by exact_mod_cast hzero
    linarith
  -- Ŝ^+ * P_{i+1} = Matrix.single i ⟨i+1⟩ c
  have hraise := spinSOpPlus_mul_diagProj_succ_eq_single (N := N) i h
  -- We show: E_{i, i+1, 1} = (1/c) • (Ŝ^+ * P_{i+1})
  have hkey : Matrix.single i (⟨i.val + 1, h⟩ : Fin (N + 1)) (1 : ℂ) =
              (1 / (c : ℂ)) • (spinSOpPlus N * spinSDiagProj N ⟨i.val + 1, h⟩) := by
    rw [hraise]
    rw [Matrix.smul_single]
    congr 1
    rw [smul_eq_mul, one_div, inv_mul_cancel₀ hc_ne]
  rw [hkey]
  refine Subalgebra.smul_mem _ ?_ _
  refine Subalgebra.mul_mem _ (spinSOpPlus_mem_adjoin N) ?_
  exact spinSDiagProj_mem_adjoin N _

/-- The matrix unit `E_{i+1, i} ∈ Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`. -/
theorem single_succ_swap_mem_adjoin (i : Fin (N + 1)) (h : i.val + 1 < N + 1) :
    Matrix.single (⟨i.val + 1, h⟩ : Fin (N + 1)) i (1 : ℂ) ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) := by
  set c : ℝ :=
    Real.sqrt (((N : ℝ) - (i.val : ℝ)) * ((i.val : ℝ) + 1))
  have hc_pos : 0 < c := by
    apply Real.sqrt_pos.mpr
    apply mul_pos
    · have : i.val + 1 ≤ N := by omega
      have : (i.val : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast this
      linarith
    · positivity
  have hc_ne : (c : ℂ) ≠ 0 := by
    intro hzero
    have : (c : ℝ) = 0 := by exact_mod_cast hzero
    linarith
  -- Ŝ^- * P_i = Matrix.single ⟨i+1⟩ i c
  have hlower := spinSOpMinus_mul_diagProj_eq_single (N := N) i h
  have hkey : Matrix.single (⟨i.val + 1, h⟩ : Fin (N + 1)) i (1 : ℂ) =
              (1 / (c : ℂ)) • (spinSOpMinus N * spinSDiagProj N i) := by
    rw [hlower]
    rw [Matrix.smul_single]
    congr 1
    rw [smul_eq_mul, one_div, inv_mul_cancel₀ hc_ne]
  rw [hkey]
  refine Subalgebra.smul_mem _ ?_ _
  refine Subalgebra.mul_mem _ (spinSOpMinus_mem_adjoin N) ?_
  exact spinSDiagProj_mem_adjoin N _

end LatticeSystem.Quantum
