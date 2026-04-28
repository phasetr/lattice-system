/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Math.PerronFrobeniusPrimitive
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.Basic

/-!
# Collatz-Wielandt function and maximizer existence

Ported and adapted from or4nge19/MCMC,
`MCMC/PF/LinearAlgebra/Matrix/PerronFrobenius/CollatzWielandt.lean`.

The Collatz-Wielandt function `r(x) = min_{i | x_i > 0} (Ax)_i / x_i` is the key tool in the
non-spectral proof of the Perron-Frobenius theorem (Seneta, §1.2).  Its upper-semicontinuity on
the standard simplex and the resulting maximizer existence (EVT for USC on compact sets) are the
main results.

## Main results

- `collatzWielandtFn`: the Collatz-Wielandt function
- `le_any_ratio`: `CW(x) ≤ (Ax)_i / x_i` for any `i` with `x_i > 0`
- `le_mulVec`: fundamental inequality `CW(x) • x ≤ A *ᵥ x`
- `smul_eq`: scale invariance `CW(c • x) = CW(x)` for `c > 0`
- `upperSemicontinuousOn`: `CW` is upper-semicontinuous on the standard simplex
- `exists_maximizer`: `CW` attains its maximum on the standard simplex
- `eq_eigenvalue`: `CW(v) = r` when `Av = r • v` and `v > 0`

## References

- E. Seneta, *Non-negative Matrices and Markov Chains* (3rd ed.), Springer 2006, §1.2 (pp. 27–28).
- or4nge19/MCMC: `MCMC/PF/LinearAlgebra/Matrix/PerronFrobenius/CollatzWielandt.lean`.
  The proof of `upperSemicontinuousOn` uses a simpler neighbourhood argument than MCMC.
-/

namespace LatticeSystem.Math.CollatzWielandt

open Matrix Finset Set Filter Topology

variable {n : Type*} [Fintype n]

/-! ## Helpers -/

private lemma exists_pos_mem_stdSimplex {x : n → ℝ} (hx : x ∈ stdSimplex ℝ n) :
    ∃ i, 0 < x i := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hzero : ∀ i, x i = 0 := fun i => le_antisymm (h i) (hx.1 i)
  linarith [hx.2, Finset.sum_eq_zero (fun i _ => hzero i) (f := x) (s := univ)]

/-- Members of the standard simplex are nonzero. -/
lemma ne_zero_of_mem_stdSimplex {x : n → ℝ} (hx : x ∈ stdSimplex ℝ n) : x ≠ 0 := by
  rintro rfl; simp [stdSimplex] at hx

omit [Fintype n] in
private lemma exists_pos_of_nonneg_ne_zero {x : n → ℝ} (hx : ∀ i, 0 ≤ x i) (hne : x ≠ 0) :
    ∃ i, 0 < x i := by
  by_contra h
  simp only [not_exists, not_lt] at h
  exact hne (funext fun i => le_antisymm (h i) (hx i))

/-! ## Definition -/

/-- Support: indices with `x_i > 0`. -/
private noncomputable def supp (x : n → ℝ) : Finset n :=
  haveI : DecidablePred (fun i : n => 0 < x i) := Classical.decPred _
  univ.filter (fun i => 0 < x i)

private lemma mem_supp {x : n → ℝ} {i : n} : i ∈ supp x ↔ 0 < x i := by
  simp [supp]

/-- The Collatz-Wielandt function: `min_{i | x_i > 0} (Ax)_i / x_i`.
Returns 0 when `x` has no positive entries.

Ref: Seneta §1.2 (p. 27); MCMC `CollatzWielandt.lean` `collatzWielandtFn`. -/
noncomputable def collatzWielandtFn (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  if h : (supp x).Nonempty then (supp x).inf' h (fun i => (A *ᵥ x) i / x i)
  else 0

/-! ## Basic properties -/

/-- `CW(x) ≤ (Ax)_i / x_i` for any `i` with `x_i > 0`.

Ref: Seneta §1.2; MCMC `CollatzWielandt.lean` `le_any_ratio`. -/
lemma le_any_ratio {A : Matrix n n ℝ} {x : n → ℝ} {i : n} (hi : 0 < x i) :
    collatzWielandtFn A x ≤ (A *ᵥ x) i / x i := by
  unfold collatzWielandtFn
  have h_supp : (supp x).Nonempty := ⟨i, mem_supp.mpr hi⟩
  rw [dif_pos h_supp]
  exact inf'_le _ (mem_supp.mpr hi)

/-- Fundamental inequality: `CW(x) • x ≤ A *ᵥ x` for nonneg `x`, `A ≥ 0`.

Ref: Seneta §1.2 (p. 27); MCMC `CollatzWielandt.lean` `le_mulVec`. -/
lemma le_mulVec {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) {x : n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    collatzWielandtFn A x • x ≤ A *ᵥ x := by
  intro i
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hi : x i = 0
  · rw [hi, mul_zero]
    simp only [mulVec, dotProduct]
    exact sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j)
  · exact (le_div_iff₀ (lt_of_le_of_ne (hx i) (Ne.symm hi))).mp
        (le_any_ratio (lt_of_le_of_ne (hx i) (Ne.symm hi)))

/-- Scale invariance: `CW(c • x) = CW(x)` for `c > 0`.

Ref: MCMC `CollatzWielandt.lean` `smul`. -/
lemma smul_eq {A : Matrix n n ℝ} {c : ℝ} (hc : 0 < c) {x : n → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hx_ne : x ≠ 0) :
    collatzWielandtFn A (c • x) = collatzWielandtFn A x := by
  obtain ⟨j, hj⟩ := exists_pos_of_nonneg_ne_zero hx hx_ne
  have h_ratio : ∀ i : n, 0 < x i →
      (A *ᵥ (c • x)) i / (c • x) i = (A *ᵥ x) i / x i := fun i hi => by
    simp only [mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_div_mul_left _ _ hc.ne'
  apply le_antisymm
  · unfold collatzWielandtFn
    have h_supp : (supp x).Nonempty := ⟨j, mem_supp.mpr hj⟩
    rw [dif_pos h_supp]
    apply le_inf'
    intro i hi
    have hxi := mem_supp.mp hi
    calc collatzWielandtFn A (c • x)
        ≤ (A *ᵥ (c • x)) i / (c • x) i :=
            le_any_ratio (by simpa [smul_eq_mul] using mul_pos hc hxi)
      _ = (A *ᵥ x) i / x i := h_ratio i hxi
  · unfold collatzWielandtFn
    have h_supp' : (supp (c • x)).Nonempty :=
      ⟨j, mem_supp.mpr (by simpa [smul_eq_mul] using mul_pos hc hj)⟩
    rw [dif_pos h_supp']
    apply le_inf'
    intro i hi
    have hxi : 0 < x i := by
      have := mem_supp.mp hi
      simpa [smul_eq_mul, mul_pos_iff_of_pos_left hc] using this
    calc collatzWielandtFn A x
        ≤ (A *ᵥ x) i / x i := le_any_ratio hxi
      _ = (A *ᵥ (c • x)) i / (c • x) i := (h_ratio i hxi).symm

/-- `CW(v) = r` when `Av = r • v` with all `v_i > 0`.

Ref: MCMC `CollatzWielandt.lean` `eq_eigenvalue_of_positive_eigenvector`. -/
lemma eq_eigenvalue [Nonempty n] {A : Matrix n n ℝ} {r : ℝ} {v : n → ℝ}
    (hv : ∀ i, 0 < v i) (h_eig : A *ᵥ v = r • v) :
    collatzWielandtFn A v = r := by
  unfold collatzWielandtFn
  have h_supp : (supp v).Nonempty :=
    ⟨Classical.arbitrary n, mem_supp.mpr (hv _)⟩
  rw [dif_pos h_supp]
  have h_ratio : ∀ i ∈ supp v, (A *ᵥ v) i / v i = r := fun i hi => by
    rw [h_eig, Pi.smul_apply, smul_eq_mul]
    exact mul_div_cancel_right₀ r (mem_supp.mp hi).ne'
  apply le_antisymm
  · calc (supp v).inf' h_supp (fun i => (A *ᵥ v) i / v i)
        ≤ (A *ᵥ v) (Classical.arbitrary n) / v (Classical.arbitrary n) :=
            inf'_le _ (mem_supp.mpr (hv _))
      _ = r := h_ratio _ (mem_supp.mpr (hv _))
  · exact le_inf' _ _ fun i hi => (h_ratio i hi).symm.le

/-! ## Upper-semicontinuity -/

/-- The CW function is upper-semicontinuous on the standard simplex.

**Proof**: Given `c > CW(x₀)`, there exists `i₀ ∈ supp(x₀)` with ratio `< c`.
The map `y ↦ (Ay)_{i₀}/y_{i₀}` is continuous at `x₀`. So eventually
`(Ay)_{i₀}/y_{i₀} < c` and `y_{i₀} > 0`. For such `y`, `CW(y) ≤ (Ay)_{i₀}/y_{i₀} < c`.

Ref: Seneta §1.2 (Appendix C, p. 28); MCMC `CollatzWielandt.lean` `upperSemicontinuousOn`. -/
theorem upperSemicontinuousOn (A : Matrix n n ℝ) :
    UpperSemicontinuousOn (collatzWielandtFn A) (stdSimplex ℝ n) := by
  intro x₀ hx₀ c hc
  obtain ⟨i_pos, hi_pos⟩ := exists_pos_mem_stdSimplex hx₀
  have h_supp : (supp x₀).Nonempty := ⟨i_pos, mem_supp.mpr hi_pos⟩
  rw [collatzWielandtFn, dif_pos h_supp] at hc
  obtain ⟨i₀, hi₀_mem, hi₀_eq⟩ := exists_mem_eq_inf' h_supp (fun i => (A *ᵥ x₀) i / x₀ i)
  have hx₀_i₀ : 0 < x₀ i₀ := mem_supp.mp hi₀_mem
  have hi₀_lt : (A *ᵥ x₀) i₀ / x₀ i₀ < c := hi₀_eq ▸ hc
  have hcont : ContinuousAt (fun y : n → ℝ => (A *ᵥ y) i₀ / y i₀) x₀ := by
    have h_num : Continuous (fun y : n → ℝ => (A *ᵥ y) i₀) := by
      simp only [mulVec, dotProduct]
      exact continuous_finset_sum _ fun j _ => (continuous_apply j).const_smul (A i₀ j)
    exact h_num.continuousAt.div (continuous_apply i₀).continuousAt hx₀_i₀.ne'
  apply ((hcont.eventually (Iio_mem_nhds hi₀_lt)).and
      ((continuous_apply i₀).continuousAt.eventually (Ioi_mem_nhds hx₀_i₀)))
    |>.filter_mono nhdsWithin_le_nhds |>.mono
  intro y ⟨hlt, hpos⟩
  exact (le_any_ratio hpos).trans_lt hlt

/-! ## Maximizer existence -/

/-- CW attains its maximum on the standard simplex (EVT for USC on compact sets).

Ref: Seneta §1.2 (p. 28); MCMC `CollatzWielandt.lean` `exists_maximizer`. -/
theorem exists_maximizer [Nonempty n] (A : Matrix n n ℝ) :
    ∃ v ∈ stdSimplex ℝ n, ∀ y ∈ stdSimplex ℝ n, collatzWielandtFn A y ≤ collatzWielandtFn A v := by
  have h_ne : (stdSimplex ℝ n).Nonempty :=
    Set.nonempty_coe_sort.mp (inferInstance : Nonempty (stdSimplex ℝ n))
  obtain ⟨v, hv_mem, hv_max⟩ :=
    (upperSemicontinuousOn A).exists_isMaxOn h_ne (isCompact_stdSimplex ℝ n)
  exact ⟨v, hv_mem, hv_max⟩

end LatticeSystem.Math.CollatzWielandt
