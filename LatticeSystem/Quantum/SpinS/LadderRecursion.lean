import LatticeSystem.Quantum.SpinS.LadderProj

/-!
# Ladder recursion `Ŝ^+ · P_{k+1} · Ŝ^- = (k+1)(N−k) · P_k`
(Tasaki §2.1 P1d''' β-7)

The triple product `Ŝ^+ · P_{k+1} · Ŝ^-` collapses to a non-zero
scalar multiple of the diagonal projector `P_k`:

  `Ŝ^+ · P_{k + 1} · Ŝ^- = (k + 1)(N − k) · P_k`,    `k.val < N`.

This is the **ladder recursion** for the projectors.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a (p. 15) and solution S.1 (p. 493).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- Auxiliary: the ladder coefficient identity in ℂ. -/
private lemma ladder_coeff_aux (a : ℕ) (hN : a + 1 ≤ N) :
    ((Real.sqrt (((a : ℝ) + 1) *
        ((N : ℝ) - ((a : ℝ) + 1) + 1)) : ℝ) : ℂ) *
      ((Real.sqrt (((N : ℝ) - (a : ℝ)) * ((a : ℝ) + 1)) : ℝ) : ℂ) =
    ((a : ℂ) + 1) * ((N : ℂ) - (a : ℂ)) := by
  have ha_le_N : a ≤ N := Nat.le_of_succ_le hN
  have ha_le_N_real : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast ha_le_N
  have h_nonneg : (0 : ℝ) ≤ ((a : ℝ) + 1) * ((N : ℝ) - (a : ℝ)) :=
    mul_nonneg (by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ (a : ℝ))])
               (by linarith)
  rw [show ((N : ℝ) - ((a : ℝ) + 1) + 1) = ((N : ℝ) - (a : ℝ)) from by ring]
  rw [show (((N : ℝ) - (a : ℝ)) * ((a : ℝ) + 1)) =
      (((a : ℝ) + 1) * ((N : ℝ) - (a : ℝ))) from by ring]
  rw [show (((Real.sqrt (((a : ℝ) + 1) * ((N : ℝ) - (a : ℝ))) : ℝ) : ℂ) *
           ((Real.sqrt (((a : ℝ) + 1) * ((N : ℝ) - (a : ℝ))) : ℝ) : ℂ) : ℂ) =
           ((((a : ℝ) + 1) * ((N : ℝ) - (a : ℝ)) : ℝ) : ℂ) from by
    rw [← Complex.ofReal_mul]; congr 1; exact Real.mul_self_sqrt h_nonneg]
  push_cast
  ring

/-- The triple product `Ŝ^+ · P_{k+1} · Ŝ^-` evaluates to the
scalar multiple `(k + 1)(N − k) · P_k`. -/
theorem spinSOpPlus_mul_diagProj_succ_mul_spinSOpMinus
    (k : Fin (N + 1)) (h : k.val + 1 < N + 1) :
    spinSOpPlus N * spinSDiagProj N ⟨k.val + 1, h⟩ * spinSOpMinus N =
      (((k.val : ℂ) + 1) * ((N : ℂ) - (k.val : ℂ))) • spinSDiagProj N k := by
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply]
  rw [Finset.sum_eq_single (⟨k.val + 1, h⟩ : Fin (N + 1))]
  rotate_left
  · intro l _ hl
    rw [spinSOpPlus_mul_diagProj_apply, if_neg hl]
    simp
  · intro hne; exact absurd (Finset.mem_univ _) hne
  rw [spinSOpPlus_mul_diagProj_apply, if_pos rfl]
  -- Goal: Ŝ^+[i, ⟨k+1⟩] * Ŝ^-[⟨k+1⟩, j] = ((k+1)(N-k)) • P_k[i, j]
  by_cases hik : i = k
  · subst hik
    have hi_raise : i.val + 1 = (⟨i.val + 1, h⟩ : Fin (N + 1)).val := rfl
    rw [spinSOpPlus_apply_raise N hi_raise]
    by_cases hjk : j = i
    · subst hjk
      have hj_lower : j.val + 1 = (⟨j.val + 1, h⟩ : Fin (N + 1)).val := rfl
      rw [spinSOpMinus_apply_lower N hj_lower]
      unfold spinSDiagProj
      rw [Matrix.diagonal_apply_eq, if_pos rfl, smul_eq_mul, mul_one]
      have hjN : j.val + 1 ≤ N := Nat.le_of_lt_succ h
      rw [show ((⟨j.val + 1, h⟩ : Fin (N + 1)).val : ℝ) = ((j.val : ℝ) + 1) from by
        push_cast; ring]
      exact ladder_coeff_aux j.val hjN
    · -- j ≠ i: Ŝ^- factor vanishes.
      have hj_no_lower : ¬ (j.val + 1 = (⟨i.val + 1, h⟩ : Fin (N + 1)).val) := by
        intro heq; apply hjk; ext; omega
      rw [spinSOpMinus_apply_other N hj_no_lower]
      unfold spinSDiagProj
      rw [Matrix.diagonal_apply]
      have hij_ne : ¬ i = j := fun heq => hjk heq.symm
      rw [if_neg hij_ne]
      simp
  · -- i ≠ k: Ŝ^+ factor vanishes.
    have hsucc : (⟨k.val + 1, h⟩ : Fin (N + 1)).val = k.val + 1 := rfl
    have hi_no_raise : ¬ (i.val + 1 = (⟨k.val + 1, h⟩ : Fin (N + 1)).val) := fun heq => by
      apply hik
      rw [hsucc] at heq
      ext
      omega
    rw [spinSOpPlus_apply_other N hi_no_raise]
    rw [zero_mul]
    unfold spinSDiagProj
    rw [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_neg hik]; simp
    · rw [if_neg hij]; simp

end LatticeSystem.Quantum
