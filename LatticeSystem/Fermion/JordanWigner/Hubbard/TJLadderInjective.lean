import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheorem
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinTotHermitian

/-!
# Tasaki 11.5: ladder injectivity on weight spaces (Prop 11.24 E5)

The SU(2) ladder norm identity, from `[Ŝ⁺, Ŝ⁻] = 2 Ŝ³` and `(Ŝ⁻)ᴴ = Ŝ⁺`:
for a weight vector `Ŝ³ v = sz • v`, `‖Ŝ⁻ v‖² = ‖Ŝ⁺ v‖² + 2 sz ‖v‖²`.

Consequences (no representation theory): `Ŝ⁻` is injective on the weight space `Ŝ³ = sz` for
`sz > 0`, and `Ŝ⁺` is injective for `sz < 0`.  These ladder injections embed each `Ŝ³`-weight space
of the ground subspace into the `Ŝ³ = ±½` weight space, giving (via E3a) the bound `finrank ≤ Ne+1`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- Adjoint move: `star (A *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (Aᴴ *ᵥ y)`. -/
private theorem dotProduct_star_mulVec {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (x y : n → ℂ) :
    star (A.mulVec x) ⬝ᵥ y = star x ⬝ᵥ (Aᴴ.mulVec y) := by
  rw [Matrix.star_mulVec, dotProduct_mulVec]

/-- `star w ⬝ᵥ w` is the real sum of squared norms (cast to `ℂ`). -/
private theorem dotProduct_star_self_ofReal {n : Type*} [Fintype n] (w : n → ℂ) :
    star w ⬝ᵥ w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
  rw [dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

/-- The real squared norm vanishes iff the vector does. -/
private theorem sum_normSq_eq_zero_iff {n : Type*} [Fintype n] {w : n → ℂ} :
    (∑ i, Complex.normSq (w i)) = 0 ↔ w = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)]
  constructor
  · intro h; funext i; exact Complex.normSq_eq_zero.mp (h i (Finset.mem_univ i))
  · intro h i _; rw [h]; simp

/-- **SU(2) ladder norm identity.**  For a weight vector `Ŝ³ v = sz • v`,
`‖Ŝ⁻ v‖² = ‖Ŝ⁺ v‖² + 2 sz ‖v‖²`. -/
theorem fermionTotalSpin_ladder_norm (N : ℕ) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (sz : ℝ)
    (hsz : (fermionTotalSpinZ N).mulVec v = (sz : ℂ) • v) :
    star ((fermionTotalSpinMinus N).mulVec v) ⬝ᵥ ((fermionTotalSpinMinus N).mulVec v) =
      star ((fermionTotalSpinPlus N).mulVec v) ⬝ᵥ ((fermionTotalSpinPlus N).mulVec v) +
        (2 * (sz : ℂ)) * (star v ⬝ᵥ v) := by
  have hcomm : fermionTotalSpinPlus N * fermionTotalSpinMinus N =
      fermionTotalSpinMinus N * fermionTotalSpinPlus N + (2 : ℂ) • fermionTotalSpinZ N := by
    have h := fermionTotalSpinPlus_commutator_fermionTotalSpinMinus N
    rwa [sub_eq_iff_eq_add'] at h
  have hMinus : star ((fermionTotalSpinMinus N).mulVec v) ⬝ᵥ
      ((fermionTotalSpinMinus N).mulVec v) =
      star v ⬝ᵥ ((fermionTotalSpinPlus N * fermionTotalSpinMinus N).mulVec v) := by
    rw [dotProduct_star_mulVec, fermionTotalSpinMinus_conjTranspose, Matrix.mulVec_mulVec]
  have hPlus : star ((fermionTotalSpinPlus N).mulVec v) ⬝ᵥ
      ((fermionTotalSpinPlus N).mulVec v) =
      star v ⬝ᵥ ((fermionTotalSpinMinus N * fermionTotalSpinPlus N).mulVec v) := by
    rw [dotProduct_star_mulVec, fermionTotalSpinPlus_conjTranspose, Matrix.mulVec_mulVec]
  rw [hMinus, hPlus, hcomm, Matrix.add_mulVec, dotProduct_add]
  congr 1
  rw [Matrix.smul_mulVec, hsz, smul_smul, dotProduct_smul, smul_eq_mul]

/-- **`Ŝ⁻` is injective on positive weight spaces.** -/
theorem fermionTotalSpinMinus_mulVec_ne_zero_of_spinZ_pos (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (sz : ℝ)
    (hsz : (fermionTotalSpinZ N).mulVec v = (sz : ℂ) • v) (hszpos : 0 < sz) (hv : v ≠ 0) :
    (fermionTotalSpinMinus N).mulVec v ≠ 0 := by
  intro h
  have hid := fermionTotalSpin_ladder_norm N v sz hsz
  rw [h, star_zero, zero_dotProduct, dotProduct_star_self_ofReal,
    dotProduct_star_self_ofReal, show (2 * (sz : ℂ)) = ((2 * sz : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_mul, ← Complex.ofReal_add] at hid
  have hreal : (∑ i, Complex.normSq ((fermionTotalSpinPlus N).mulVec v i)) +
      2 * sz * (∑ i, Complex.normSq (v i)) = 0 := by exact_mod_cast hid.symm
  have hA : (0 : ℝ) ≤ ∑ i, Complex.normSq ((fermionTotalSpinPlus N).mulVec v i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hD : (0 : ℝ) ≤ ∑ i, Complex.normSq (v i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hDle : (∑ i, Complex.normSq (v i)) ≤ 0 := by
    by_contra hp; rw [not_le] at hp
    nlinarith [hreal, hA, mul_pos (by linarith : (0 : ℝ) < 2 * sz) hp]
  exact hv (sum_normSq_eq_zero_iff.mp (le_antisymm hDle hD))

/-- **`Ŝ⁺` is injective on negative weight spaces.** -/
theorem fermionTotalSpinPlus_mulVec_ne_zero_of_spinZ_neg (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (sz : ℝ)
    (hsz : (fermionTotalSpinZ N).mulVec v = (sz : ℂ) • v) (hszneg : sz < 0) (hv : v ≠ 0) :
    (fermionTotalSpinPlus N).mulVec v ≠ 0 := by
  intro h
  have hid := fermionTotalSpin_ladder_norm N v sz hsz
  rw [h, star_zero, zero_dotProduct, dotProduct_star_self_ofReal,
    dotProduct_star_self_ofReal, zero_add,
    show (2 * (sz : ℂ)) = ((2 * sz : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul] at hid
  have hreal : (∑ i, Complex.normSq ((fermionTotalSpinMinus N).mulVec v i)) =
      2 * sz * (∑ i, Complex.normSq (v i)) := by exact_mod_cast hid
  have hA : (0 : ℝ) ≤ ∑ i, Complex.normSq ((fermionTotalSpinMinus N).mulVec v i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hD : (0 : ℝ) ≤ ∑ i, Complex.normSq (v i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hDle : (∑ i, Complex.normSq (v i)) ≤ 0 := by
    by_contra hp; rw [not_le] at hp
    nlinarith [hreal, hA, mul_neg_of_neg_of_pos (by linarith : (2 * sz : ℝ) < 0) hp]
  exact hv (sum_normSq_eq_zero_iff.mp (le_antisymm hDle hD))

end LatticeSystem.Fermion
