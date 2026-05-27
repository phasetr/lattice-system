import LatticeSystem.Quantum.SpinS.SpinSTransverseLadder
import LatticeSystem.Quantum.SpinS.AxisSwappedAnisotropicHeisenberg
import LatticeSystem.Quantum.SpinS.PlusMinusDiag

/-!
# Single-ion `(Ŝ²)²`: ladder form, off-diagonal sign, and parity vanishing

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The single-site square `(Ŝ²)²` rewrites in raising/lowering form as
`¼(Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺) − ¼(Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻)`.  Consequences collected here:

* its off-diagonal (`i ≠ j`) entries are **real and `≤ 0`** (the `Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺` part is diagonal,
  the `Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻` part is real non-negative, with coefficient `−¼`);
* they **vanish when `i.val + j.val` is odd** (`(Ŝ²)²` connects only `Δ ∈ {0, ±2}`).

With the crystal-field coefficient `D ≥ 0` (case (i)) and the same-site Marshall sign `+1` (the
`±2` shift is even), this gives the non-positive dressed single-ion off-diagonal contribution to
`Ĥ'`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Ladder form -/

/-- **Ladder form of the single-site square** `(Ŝ²)²`:
`Ŝ²_x Ŝ²_x = ¼(Ŝ⁺Ŝ⁻ + Ŝ⁻Ŝ⁺) − ¼(Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻)`. -/
theorem spinSOp2_mul_spinSOp2_ladder_form (N : ℕ) :
    spinSOp2 N * spinSOp2 N =
      (1 / 4 : ℂ) • (spinSOpPlus N * spinSOpMinus N + spinSOpMinus N * spinSOpPlus N) -
        (1 / 4 : ℂ) • (spinSOpPlus N * spinSOpPlus N + spinSOpMinus N * spinSOpMinus N) := by
  have hadd := spinSOp1_mul_spinSOp1_add_spinSOp2_mul_spinSOp2 N
  have hsub := spinSOp1_mul_spinSOp1_sub_spinSOp2_mul_spinSOp2 N
  linear_combination (norm := module) (1 / 2 : ℂ) • hadd - (1 / 2 : ℂ) • hsub

/-- **Ladder form of the single-ion anisotropy term**:
`D Σ_x (Ŝ²_x)² = D Σ_x [ ¼(Ŝ⁺_x Ŝ⁻_x + Ŝ⁻_x Ŝ⁺_x) − ¼(Ŝ⁺_x Ŝ⁺_x + Ŝ⁻_x Ŝ⁻_x) ]`.
The `−¼(Ŝ⁺_x Ŝ⁺_x + Ŝ⁻_x Ŝ⁻_x)` part is the same-site `±2` parity coupling. -/
theorem singleIonAnisotropyS2_ladder_form (D : ℂ) (N : ℕ) :
    singleIonAnisotropyS2 (Λ := Λ) D N =
      D • ∑ x : Λ, onSiteS x
        ((1 / 4 : ℂ) • (spinSOpPlus N * spinSOpMinus N + spinSOpMinus N * spinSOpPlus N) -
          (1 / 4 : ℂ) • (spinSOpPlus N * spinSOpPlus N + spinSOpMinus N * spinSOpMinus N)) := by
  rw [singleIonAnisotropyS2]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [onSiteS_mul_onSiteS_same, spinSOp2_mul_spinSOp2_ladder_form]

/-! ## Off-diagonal sign -/

/-- The square of a real-entry matrix has real entries. -/
theorem matrix_mul_self_apply_im_zero {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : ∀ i j, (A i j).im = 0) (i j : n) :
    ((A * A) i j).im = 0 := by
  rw [Matrix.mul_apply, Complex.im_sum]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [Complex.mul_im, hA, hA, mul_zero, zero_mul, add_zero]

/-- The square of a real, entrywise-non-negative matrix has non-negative entries. -/
theorem matrix_mul_self_apply_re_nonneg {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : ∀ i j, (A i j).im = 0) (hAnn : ∀ i j, 0 ≤ (A i j).re) (i j : n) :
    0 ≤ ((A * A) i j).re := by
  rw [Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_nonneg (fun k _ => ?_)
  rw [Complex.mul_re, hA, zero_mul, sub_zero]
  exact mul_nonneg (hAnn _ _) (hAnn _ _)

/-- Off-diagonal value of the single-site `(Ŝ²)²`: only the `−¼(Ŝ⁺Ŝ⁺ + Ŝ⁻Ŝ⁻)` part survives. -/
theorem spinSOp2_mul_spinSOp2_apply_offdiag_eq (N : ℕ) {i j : Fin (N + 1)} (hij : i ≠ j) :
    (spinSOp2 N * spinSOp2 N) i j =
      -(1 / 4 : ℂ) * ((spinSOpPlus N * spinSOpPlus N) i j +
        (spinSOpMinus N * spinSOpMinus N) i j) := by
  rw [spinSOp2_mul_spinSOp2_ladder_form, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul, Matrix.add_apply, Matrix.add_apply,
    spinSOpPlus_mul_spinSOpMinus_eq_diagonal, spinSOpMinus_mul_spinSOpPlus_eq_diagonal,
    Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
  ring

/-- The single-site `(Ŝ²)²` off-diagonal entries are real (`im = 0`). -/
theorem spinSOp2_mul_spinSOp2_apply_offdiag_im_zero (N : ℕ) {i j : Fin (N + 1)} (hij : i ≠ j) :
    ((spinSOp2 N * spinSOp2 N) i j).im = 0 := by
  rw [spinSOp2_mul_spinSOp2_apply_offdiag_eq N hij, Complex.mul_im, Complex.add_im,
    matrix_mul_self_apply_im_zero (spinSOpPlus_apply_im_zero N),
    matrix_mul_self_apply_im_zero (spinSOpMinus_apply_im_zero N)]
  simp

/-- The single-site `(Ŝ²)²` off-diagonal entries have non-positive real part. -/
theorem spinSOp2_mul_spinSOp2_apply_offdiag_re_nonpos (N : ℕ) {i j : Fin (N + 1)} (hij : i ≠ j) :
    ((spinSOp2 N * spinSOp2 N) i j).re ≤ 0 := by
  rw [spinSOp2_mul_spinSOp2_apply_offdiag_eq N hij, Complex.mul_re]
  have hz : 0 ≤ ((spinSOpPlus N * spinSOpPlus N) i j +
      (spinSOpMinus N * spinSOpMinus N) i j).re := by
    rw [Complex.add_re]
    exact add_nonneg
      (matrix_mul_self_apply_re_nonneg (spinSOpPlus_apply_im_zero N)
        (spinSOpPlus_apply_re_nonneg N) i j)
      (matrix_mul_self_apply_re_nonneg (spinSOpMinus_apply_im_zero N)
        (spinSOpMinus_apply_re_nonneg N) i j)
  have hcre : (-(1 / 4 : ℂ)).re = -(1 / 4) := by simp
  have hcim : (-(1 / 4 : ℂ)).im = 0 := by simp
  rw [hcre, hcim, zero_mul, sub_zero]
  nlinarith [hz]

/-! ## Parity vanishing -/

/-- `(Ŝ⁺)²_{i j}` vanishes unless `j` is two steps above `i`. -/
theorem spinSOpPlus_mul_spinSOpPlus_apply_eq_zero_of_ne (N : ℕ) {i j : Fin (N + 1)}
    (hij : i.val + 2 ≠ j.val) : (spinSOpPlus N * spinSOpPlus N) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  by_cases hik : i.val + 1 = k.val
  · rw [spinSOpPlus_apply_other N (by omega : k.val + 1 ≠ j.val), mul_zero]
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
