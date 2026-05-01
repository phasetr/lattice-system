/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SpinS.Operators

/-!
# `Ŝ^- · Ŝ^+ = diag(i (N − i + 1))` for spin-`S`
(Tasaki §2.1 P1d''' β-13)

The product `Ŝ^- · Ŝ^+` is a diagonal matrix with entries the
ladder coefficient products:

  `(Ŝ^- · Ŝ^+)[i, i] = i · (N − i + 1)` (vanishes at `i = 0`),
  `(Ŝ^- · Ŝ^+)[i, j] = 0` for `i ≠ j`.

This follows from the sub/super-diagonal structure of `Ŝ^±`: the
product `Σ_l Ŝ^-[i, l] · Ŝ^+[l, j]` is non-zero only when `l + 1 = i`
AND `l + 1 = j`, forcing `i = j` (and `l = i − 1`, requiring `i ≥ 1`).

Combined with `Ŝ^+ · Ŝ^- = diag((i + 1)(N − i))` (β-12), the sum
`Ŝ^+ · Ŝ^- + Ŝ^- · Ŝ^+ = diag(2 i (N − i) + N)`, which integrates
into the Casimir identity together with `(Ŝ^{(3)})² = diag((N/2 − i)²)`
(β-11).

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- Auxiliary: `√((N − (i − 1))((i − 1) + 1)) · √(i · (N − i + 1)) = i · (N − i + 1)` (in ℂ),
for `i ≥ 1`. -/
private lemma minusPlus_diag_aux (i : ℕ) (_hi : i ≥ 1) (hN : i ≤ N) :
    ((Real.sqrt (((N : ℝ) - ((i : ℝ) - 1)) * (((i : ℝ) - 1) + 1)) : ℝ) : ℂ) *
      ((Real.sqrt ((i : ℝ) * ((N : ℝ) - (i : ℝ) + 1)) : ℝ) : ℂ) =
    ((i : ℂ) * ((N : ℂ) - (i : ℂ) + 1)) := by
  have hi_le_N_real : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h_nonneg : (0 : ℝ) ≤ (i : ℝ) * ((N : ℝ) - (i : ℝ) + 1) :=
    mul_nonneg (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))])
               (by linarith)
  rw [show (((N : ℝ) - ((i : ℝ) - 1)) * (((i : ℝ) - 1) + 1)) =
      ((i : ℝ) * ((N : ℝ) - (i : ℝ) + 1)) from by ring]
  rw [show (((Real.sqrt ((i : ℝ) * ((N : ℝ) - (i : ℝ) + 1)) : ℝ) : ℂ) *
           ((Real.sqrt ((i : ℝ) * ((N : ℝ) - (i : ℝ) + 1)) : ℝ) : ℂ)) =
           (((i : ℝ) * ((N : ℝ) - (i : ℝ) + 1) : ℝ) : ℂ) from by
    rw [← Complex.ofReal_mul]; congr 1; exact Real.mul_self_sqrt h_nonneg]
  push_cast
  ring

/-- `Ŝ^- · Ŝ^+ = diag(i · (N − i + 1))`. -/
theorem spinSOpMinus_mul_spinSOpPlus_eq_diagonal (N : ℕ) :
    spinSOpMinus N * spinSOpPlus N =
      Matrix.diagonal (fun i : Fin (N + 1) =>
        (((i.val : ℂ)) * ((N : ℂ) - (i.val : ℂ) + 1))) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi_pos : 0 < i.val
    · -- valid `l = ⟨i.val - 1, _⟩`.
      have hi_lt : i.val - 1 < N + 1 := by
        have : i.val ≤ N := Nat.le_of_lt_succ i.isLt
        omega
      rw [Finset.sum_eq_single (⟨i.val - 1, hi_lt⟩ : Fin (N + 1))]
      · have hpred_succ : (⟨i.val - 1, hi_lt⟩ : Fin (N + 1)).val + 1 = i.val := by
          simp; omega
        rw [spinSOpMinus_apply_lower N hpred_succ]
        rw [spinSOpPlus_apply_raise N hpred_succ]
        have hpred_real : ((⟨i.val - 1, hi_lt⟩ : Fin (N + 1)).val : ℝ) = (i.val : ℝ) - 1 := by
          push_cast
          have : (((i.val - 1 : ℕ) : ℝ) : ℝ) = (i.val : ℝ) - 1 := by
            have : ((i.val - 1 : ℕ) : ℝ) = (i.val : ℝ) - 1 := by
              rw [show i.val - 1 = i.val - 1 from rfl]
              exact_mod_cast Nat.cast_sub hi_pos
            exact this
          omega
        rw [show ((⟨i.val - 1, hi_lt⟩ : Fin (N + 1)).val : ℝ) = (i.val : ℝ) - 1 from hpred_real]
        rw [show ((i.val : ℝ) : ℝ) = (i.val : ℝ) from rfl]
        have hN1 : i.val ≤ N := Nat.le_of_lt_succ i.isLt
        rw [show (i.val : ℝ) * ((N : ℝ) - (i.val : ℝ) + 1) =
              (i.val : ℝ) * ((N : ℝ) - (i.val : ℝ) + 1) from rfl]
        exact minusPlus_diag_aux i.val hi_pos hN1
      · intro l _ hl
        have h_no_lower : ¬ (l.val + 1 = i.val) := fun heq => by
          apply hl
          apply Fin.ext
          change l.val = i.val - 1
          omega
        rw [spinSOpMinus_apply_other N h_no_lower]
        ring
      · intro hne; exact absurd (Finset.mem_univ _) hne
    · -- i.val = 0: no valid l, sum = 0; RHS = 0.
      push Not at hi_pos
      have hi_eq : i.val = 0 := by omega
      refine (Finset.sum_eq_zero fun l _ => ?_).trans ?_
      · have h_no_lower : ¬ (l.val + 1 = i.val) := by
          rw [hi_eq]; omega
        rw [spinSOpMinus_apply_other N h_no_lower]
        ring
      · rw [hi_eq]; push_cast; ring
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h_lower : l.val + 1 = i.val
    · have h_no_raise : ¬ (l.val + 1 = j.val) := by
        intro heq
        apply hij
        ext
        omega
      rw [spinSOpPlus_apply_other N h_no_raise]
      ring
    · rw [spinSOpMinus_apply_other N h_lower]
      ring

end LatticeSystem.Quantum
