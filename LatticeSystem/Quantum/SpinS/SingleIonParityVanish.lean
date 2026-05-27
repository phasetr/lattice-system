import LatticeSystem.Quantum.SpinS.SingleIonSqSign

/-!
# Parity vanishing of the single-site `(Ŝ²)²` entries

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The single-site square `(Ŝ²)²` connects levels differing by `0` or `±2` only: `Ŝ⁺Ŝ⁺` raises by `2`,
`Ŝ⁻Ŝ⁻` lowers by `2`, `Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺` is diagonal.  Hence `(Ŝ²)²_{i j}` vanishes whenever
`i.val + j.val` is **odd** (a difference of opposite parity).  This is what makes the same-site
Marshall sign `(−1)^{σ'_x + σ_x}` equal to `+1` on the support of the single-ion term — so the
dressed single-ion off-diagonal entries keep the sign `−D/4 ≤ 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- `(Ŝ⁺)²_{i j}` vanishes unless `j` is two steps above `i`. -/
theorem spinSOpPlus_mul_spinSOpPlus_apply_eq_zero_of_ne (N : ℕ) {i j : Fin (N + 1)}
    (hij : i.val + 2 ≠ j.val) : (spinSOpPlus N * spinSOpPlus N) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  by_cases hik : i.val + 1 = k.val
  · -- then for the second factor to be non-zero need k.val + 1 = j.val, i.e. i.val + 2 = j.val.
    rw [spinSOpPlus_apply_other N (by omega : k.val + 1 ≠ j.val), mul_zero]
  · rw [spinSOpPlus_apply_other N hik, zero_mul]

/-- `(Ŝ⁻)²_{i j}` vanishes unless `i` is two steps above `j`. -/
theorem spinSOpMinus_mul_spinSOpMinus_apply_eq_zero_of_ne (N : ℕ) {i j : Fin (N + 1)}
    (hij : j.val + 2 ≠ i.val) : (spinSOpMinus N * spinSOpMinus N) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  by_cases hik : k.val + 1 = i.val
  · rw [spinSOpMinus_apply_other N (by omega : j.val + 1 ≠ k.val), mul_zero]
  · rw [spinSOpMinus_apply_other N (by omega : k.val + 1 ≠ i.val), zero_mul]

/-- The single-site `(Ŝ²)²` entries vanish when `i.val + j.val` is odd. -/
theorem spinSOp2_mul_spinSOp2_apply_eq_zero_of_odd (N : ℕ) {i j : Fin (N + 1)}
    (hpar : Odd (i.val + j.val)) : (spinSOp2 N * spinSOp2 N) i j = 0 := by
  obtain ⟨m, hm⟩ := hpar
  have hij : i ≠ j := fun h => by subst h; omega
  rw [spinSOp2_mul_spinSOp2_apply_offdiag_eq N hij,
    spinSOpPlus_mul_spinSOpPlus_apply_eq_zero_of_ne N (by omega),
    spinSOpMinus_mul_spinSOpMinus_apply_eq_zero_of_ne N (by omega)]
  ring

end LatticeSystem.Quantum
