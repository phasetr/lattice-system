import LatticeSystem.Quantum.SpinS.Operators

/-!
# `Ŝ^+ · Ŝ^- = diag((i + 1)(N − i))` for spin-`S`
(Tasaki §2.1 P1d''' β-12)

The product `Ŝ^+ · Ŝ^-` is a diagonal matrix with entries the
ladder coefficient products `(i + 1)(N − i)`:

  `(Ŝ^+ · Ŝ^-)[i, i] = (i + 1)(N − i)` (vanishes at `i = N`),
  `(Ŝ^+ · Ŝ^-)[i, j] = 0` for `i ≠ j`.

This follows from the sub/super-diagonal structure of `Ŝ^±`: the
product `Σ_l Ŝ^+[i, l] · Ŝ^-[l, j]` is non-zero only when `l = i + 1`
AND `l = j + 1`, forcing `i = j`.

This is the key matrix-product computation toward the **Casimir
identity** `(Ŝ^{(1)})² + (Ŝ^{(2)})² + (Ŝ^{(3)})² = (N(N+2)/4) · 1`,
which combines `Ŝ^+ · Ŝ^- + Ŝ^- · Ŝ^+ = 2 · (Ŝ^{(1)})² + 2 · (Ŝ^{(2)})²`
with `(Ŝ^{(3)})²` (β-11).

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- Auxiliary: `√((i + 1)(N − i)) · √((N − i)(i + 1)) = (i + 1)(N − i)` (in ℂ). -/
private lemma plusMinus_diag_aux (i : ℕ) (hN : i + 1 ≤ N) :
    ((Real.sqrt (((i : ℝ) + 1) * ((N : ℝ) - (i : ℝ))) : ℝ) : ℂ) *
      ((Real.sqrt (((N : ℝ) - (i : ℝ)) * ((i : ℝ) + 1)) : ℝ) : ℂ) =
    ((i : ℂ) + 1) * ((N : ℂ) - (i : ℂ)) := by
  have hi_le_N : i ≤ N := Nat.le_of_succ_le hN
  have hi_le_N_real : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi_le_N
  have h_nonneg : (0 : ℝ) ≤ ((i : ℝ) + 1) * ((N : ℝ) - (i : ℝ)) :=
    mul_nonneg (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ (i : ℝ))])
               (by linarith)
  rw [show (((N : ℝ) - (i : ℝ)) * ((i : ℝ) + 1)) =
      (((i : ℝ) + 1) * ((N : ℝ) - (i : ℝ))) from by ring]
  rw [show (((Real.sqrt (((i : ℝ) + 1) * ((N : ℝ) - (i : ℝ))) : ℝ) : ℂ) *
           ((Real.sqrt (((i : ℝ) + 1) * ((N : ℝ) - (i : ℝ))) : ℝ) : ℂ)) =
           ((((i : ℝ) + 1) * ((N : ℝ) - (i : ℝ)) : ℝ) : ℂ) from by
    rw [← Complex.ofReal_mul]; congr 1; exact Real.mul_self_sqrt h_nonneg]
  push_cast
  ring

/-- `Ŝ^+ · Ŝ^- = diag((i + 1)(N − i))`. -/
theorem spinSOpPlus_mul_spinSOpMinus_eq_diagonal (N : ℕ) :
    spinSOpPlus N * spinSOpMinus N =
      Matrix.diagonal (fun i : Fin (N + 1) =>
        (((i.val : ℂ) + 1) * ((N : ℂ) - (i.val : ℂ)))) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi_succ : i.val + 1 < N + 1
    · -- valid `l = ⟨i.val + 1, hi_succ⟩`.
      rw [Finset.sum_eq_single (⟨i.val + 1, hi_succ⟩ : Fin (N + 1))]
      · have hraise : i.val + 1 = (⟨i.val + 1, hi_succ⟩ : Fin (N + 1)).val := rfl
        have hlower : i.val + 1 = (⟨i.val + 1, hi_succ⟩ : Fin (N + 1)).val := rfl
        rw [spinSOpPlus_apply_raise N hraise]
        rw [spinSOpMinus_apply_lower N hlower]
        have hsucc : ((⟨i.val + 1, hi_succ⟩ : Fin (N + 1)).val : ℝ) = (i.val : ℝ) + 1 := by
          push_cast; ring
        have hN1 : i.val + 1 ≤ N := Nat.le_of_lt_succ hi_succ
        rw [show ((⟨i.val + 1, hi_succ⟩ : Fin (N + 1)).val : ℝ) *
              ((N : ℝ) - ((⟨i.val + 1, hi_succ⟩ : Fin (N + 1)).val : ℝ) + 1) =
              ((i.val : ℝ) + 1) * ((N : ℝ) - (i.val : ℝ)) from by
          rw [hsucc]; ring]
        exact plusMinus_diag_aux i.val hN1
      · -- other l: zero contribution.
        intro l _ hl
        have h_no_raise : ¬ (i.val + 1 = l.val) := fun heq => hl (Fin.ext heq.symm)
        rw [spinSOpPlus_apply_other N
            (fun heq => h_no_raise (by
              have : l.val = i.val + 1 := by
                have hlsucc : l.val = (⟨i.val + 1, hi_succ⟩ : Fin (N + 1)).val := by
                  -- heq : i.val + 1 = l.val, but we want l.val = i.val + 1
                  exact heq.symm
                exact hlsucc.trans rfl
              exact this.symm))]
        ring
      · intro hne; exact absurd (Finset.mem_univ _) hne
    · -- i.val + 1 = N + 1, i.e., i = Fin.last N: sum vanishes; RHS = 0.
      push Not at hi_succ
      have hi_eq : i.val = N := by omega
      refine (Finset.sum_eq_zero fun l _ => ?_).trans ?_
      · -- Ŝ^+[i, l] = 0 for i = Fin.last N.
        have : l.val ≤ N := Nat.le_of_lt_succ l.isLt
        have h_no_raise : ¬ (i.val + 1 = l.val) := by
          rw [hi_eq]; omega
        rw [spinSOpPlus_apply_other N h_no_raise]
        ring
      · rw [hi_eq]; ring
  · rw [if_neg hij]
    -- i ≠ j: no l satisfies both raise and lower conditions.
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h_raise : i.val + 1 = l.val
    · -- Then need l.val = j.val + 1, i.e., i = j. Contradiction.
      have h_no_lower : ¬ (j.val + 1 = l.val) := by
        intro heq
        apply hij
        ext
        omega
      rw [spinSOpMinus_apply_other N h_no_lower]
      ring
    · rw [spinSOpPlus_apply_other N h_raise]
      ring

end LatticeSystem.Quantum
