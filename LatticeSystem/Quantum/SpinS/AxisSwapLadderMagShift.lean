import LatticeSystem.Quantum.SpinS.AxisSwapLadderForm
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.MultiSiteCommutator
import LatticeSystem.Quantum.SpinS.Algebra

/-!
# Magnetization shifts of the axis-swapped ladder bond terms (parity preservation)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The ladder form (2.5.16) of the axis-swapped bond couples magnetization sectors only through the
operators `Ŝ⁺_x Ŝ⁻_y`, `Ŝ⁻_x Ŝ⁺_y` (which preserve `Ŝ³_tot`) and `Ŝ⁺_x Ŝ⁺_y`, `Ŝ⁻_x Ŝ⁻_y` (which
shift `Ŝ³_tot` by `+2`, `−2`).  Hence every term changes the total magnetization by an even
amount, so `Ĥ'` preserves the **even/odd parity** of the magnetization — the structure that lets
the Marshall-sign Perron–Frobenius argument bound the degeneracy by `2`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43 (eq. 2.5.16).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Generic two-factor magnetization shift: if `Ŝ³_tot A = A Ŝ³_tot + a•A` and
`Ŝ³_tot B = B Ŝ³_tot + b•B`, then `Ŝ³_tot (A B) = (A B) Ŝ³_tot + (a+b)•(A B)`. -/
private theorem totalSpinSOp3_mul_of_shift {A B : ManyBodyOpS Λ N} {a b : ℂ}
    (hA : totalSpinSOp3 Λ N * A = A * totalSpinSOp3 Λ N + a • A)
    (hB : totalSpinSOp3 Λ N * B = B * totalSpinSOp3 Λ N + b • B) :
    totalSpinSOp3 Λ N * (A * B) = (A * B) * totalSpinSOp3 Λ N + (a + b) • (A * B) := by
  have e1 : totalSpinSOp3 Λ N * (A * B) = A * (totalSpinSOp3 Λ N * B) + a • (A * B) := by
    rw [← mul_assoc, hA, add_mul, smul_mul_assoc, mul_assoc]
  rw [e1, hB, mul_add, ← mul_assoc, mul_smul_comm, add_smul]
  abel

/-- Single-site shift: `Ŝ³_tot (onSiteS x Ŝ⁺) = (onSiteS x Ŝ⁺) Ŝ³_tot + onSiteS x Ŝ⁺`. -/
theorem totalSpinSOp3_mul_onSiteS_spinSOpPlus (x : Λ) :
    totalSpinSOp3 Λ N * onSiteS x (spinSOpPlus N) =
      onSiteS x (spinSOpPlus N) * totalSpinSOp3 Λ N + (1 : ℂ) • onSiteS x (spinSOpPlus N) := by
  have h := onSiteS_commutator_totalOnSiteS (Λ := Λ) x (spinSOpPlus N) (spinSOp3 N)
  have hcart : spinSOpPlus N * spinSOp3 N - spinSOp3 N * spinSOpPlus N = -spinSOpPlus N := by
    have hc := spinSOp3_commutator_spinSOpPlus N
    linear_combination (norm := abel) -hc
  rw [hcart, onSiteS_neg] at h
  rw [totalSpinSOp3, one_smul]
  linear_combination (norm := abel) -h

/-- Single-site shift: `Ŝ³_tot (onSiteS x Ŝ⁻) = (onSiteS x Ŝ⁻) Ŝ³_tot − onSiteS x Ŝ⁻`. -/
theorem totalSpinSOp3_mul_onSiteS_spinSOpMinus (x : Λ) :
    totalSpinSOp3 Λ N * onSiteS x (spinSOpMinus N) =
      onSiteS x (spinSOpMinus N) * totalSpinSOp3 Λ N + (-1 : ℂ) • onSiteS x (spinSOpMinus N) := by
  have h := onSiteS_commutator_totalOnSiteS (Λ := Λ) x (spinSOpMinus N) (spinSOp3 N)
  have hcart : spinSOpMinus N * spinSOp3 N - spinSOp3 N * spinSOpMinus N = spinSOpMinus N := by
    have hc := spinSOp3_commutator_spinSOpMinus N
    linear_combination (norm := abel) -hc
  rw [hcart] at h
  rw [totalSpinSOp3, neg_one_smul]
  linear_combination (norm := abel) -h

/-- `Ŝ⁺_x Ŝ⁺_y` shifts the magnetization by `+2`. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpPlus_mulVec_mem_magSubspaceS
    (x y : Λ) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ magSubspaceS Λ N M) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpPlus N)).mulVec v ∈
      magSubspaceS Λ N (M + 2) := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  have hcomm := totalSpinSOp3_mul_of_shift (totalSpinSOp3_mul_onSiteS_spinSOpPlus (N := N) x)
    (totalSpinSOp3_mul_onSiteS_spinSOpPlus (N := N) y)
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, Matrix.smul_mulVec, ← add_smul]
  congr 1; ring

/-- `Ŝ⁻_x Ŝ⁻_y` shifts the magnetization by `−2`. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpMinus_mulVec_mem_magSubspaceS
    (x y : Λ) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ magSubspaceS Λ N M) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpMinus N)).mulVec v ∈
      magSubspaceS Λ N (M - 2) := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  have hcomm := totalSpinSOp3_mul_of_shift (totalSpinSOp3_mul_onSiteS_spinSOpMinus (N := N) x)
    (totalSpinSOp3_mul_onSiteS_spinSOpMinus (N := N) y)
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, Matrix.smul_mulVec, ← add_smul]
  congr 1; ring

/-- `Ŝ⁺_x Ŝ⁻_y` preserves the magnetization. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_mulVec_mem_magSubspaceS
    (x y : Λ) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ magSubspaceS Λ N M) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)).mulVec v ∈ magSubspaceS Λ N M := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  have hcomm := totalSpinSOp3_mul_of_shift (totalSpinSOp3_mul_onSiteS_spinSOpPlus (N := N) x)
    (totalSpinSOp3_mul_onSiteS_spinSOpMinus (N := N) y)
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, Matrix.smul_mulVec, ← add_smul]
  congr 1; ring

/-- `Ŝ⁻_x Ŝ⁺_y` preserves the magnetization. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_mulVec_mem_magSubspaceS
    (x y : Λ) {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ} (hv : v ∈ magSubspaceS Λ N M) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)).mulVec v ∈ magSubspaceS Λ N M := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  have hcomm := totalSpinSOp3_mul_of_shift (totalSpinSOp3_mul_onSiteS_spinSOpMinus (N := N) x)
    (totalSpinSOp3_mul_onSiteS_spinSOpPlus (N := N) y)
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, Matrix.smul_mulVec, ← add_smul]
  congr 1; ring

end LatticeSystem.Quantum
