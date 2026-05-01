import LatticeSystem.Quantum.SpinS.Operators

/-!
# Spin-`S` ladder action on basis vectors (Tasaki §2.1 P1d''' β-16)

The raising and lowering operators `Ŝ^±` act on the unit basis
vectors `|k⟩ = Pi.single k 1` of `(Fin (N + 1) → ℂ)` as follows:

  `Ŝ^+ · |k⟩ = √(k · (N − k + 1)) · |k − 1⟩` (for `k ≥ 1`),
  `Ŝ^- · |k⟩ = √((N − k) · (k + 1)) · |k + 1⟩` (for `k ≤ N − 1`).

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- Raising-action lemma: `Ŝ^+ · |k⟩ = √(k(N − k + 1)) · |k − 1⟩` for `k ≥ 1`. -/
theorem spinSOpPlus_mulVec_basis (N : ℕ) (k : Fin (N + 1)) (h : 0 < k.val) :
    (spinSOpPlus N).mulVec (Pi.single k 1) =
      ((Real.sqrt (((k.val : ℝ)) * ((N : ℝ) - (k.val : ℝ) + 1)) : ℝ) : ℂ) •
        (Pi.single ⟨k.val - 1, by have := k.isLt; omega⟩ 1 :
          Fin (N + 1) → ℂ) := by
  rw [Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply]
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hpred : i.val + 1 = k.val
  · rw [spinSOpPlus_apply_raise N hpred]
    have hi_eq : i = ⟨k.val - 1, by have := k.isLt; omega⟩ := by
      apply Fin.ext
      change i.val = k.val - 1
      omega
    rw [hi_eq, Pi.single_eq_same, mul_one]
  · rw [spinSOpPlus_apply_other N hpred]
    have hi_ne : i ≠ ⟨k.val - 1, by have := k.isLt; omega⟩ := by
      intro heq
      apply hpred
      have h2 := congrArg Fin.val heq
      change i.val = k.val - 1 at h2
      omega
    simp [Pi.single, Function.update, hi_ne]

/-- Lowering-action lemma: `Ŝ^- · |k⟩ = √((N − k)(k + 1)) · |k + 1⟩`
for `k.val + 1 ≤ N`. -/
theorem spinSOpMinus_mulVec_basis (N : ℕ) (k : Fin (N + 1))
    (h : k.val + 1 < N + 1) :
    (spinSOpMinus N).mulVec (Pi.single k 1) =
      ((Real.sqrt (((N : ℝ) - (k.val : ℝ)) * ((k.val : ℝ) + 1)) : ℝ) : ℂ) •
        (Pi.single ⟨k.val + 1, h⟩ 1 : Fin (N + 1) → ℂ) := by
  rw [Matrix.mulVec_single_one]
  funext i
  rw [Matrix.col_apply]
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hsucc : k.val + 1 = i.val
  · rw [spinSOpMinus_apply_lower N hsucc]
    have hi_eq : i = ⟨k.val + 1, h⟩ := by
      apply Fin.ext
      change i.val = k.val + 1
      omega
    rw [hi_eq, Pi.single_eq_same, mul_one]
  · rw [spinSOpMinus_apply_other N hsucc]
    have hi_ne : i ≠ ⟨k.val + 1, h⟩ := by
      intro heq
      apply hsucc
      have h2 := congrArg Fin.val heq
      change i.val = k.val + 1 at h2
      omega
    simp [Pi.single, Function.update, hi_ne]

end LatticeSystem.Quantum
