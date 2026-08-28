import LatticeSystem.Math.Combinatorics.ChooseConfigFiber
import LatticeSystem.Quantum.SpinS.SaturatedCoherentWeight

/-!
# Closed component form of the saturated-ferromagnet ladder iterates

The magnetisation-sector ground states of the saturated ferromagnet are the normalised iterates
`Φ_M = (Ŝ_tot^-)^k Φ↑ / ‖(Ŝ_tot^-)^k Φ↑‖` with `k = |Λ|S - M`
(`saturatedWeightVector`, Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
eq. (2.4.9), p. 33).  This module evaluates all three ingredients in closed form:

* the unnormalised iterate is supported on the configurations of total lowering count `k`, where
  it takes the value `k! · ∏_x √(binom N σ_x)`;
* its `ℓ²` norm is `k! · √(binom (|Λ| N) k)`;
* hence the sector state itself is `(√(binom (|Λ| N) k))⁻¹ · ∏_x √(binom N σ_x)` on that fiber
  and `0` off it.

The last statement is eq. (2.4.11), p. 34, in its general-`S` form.  Tasaki states (2.4.11) for
`S = 1/2`, where every one-site weight `binom 1 σ_x` is `1` and the formula reduces to the printed
uniform weight `√[(S_max+M)!(S_max−M)!/(2S_max)!]` shared by all configurations of the sector; for
`S > 1/2` the site weights are genuinely present.

The induction on `k` peels one `Ŝ_tot^-` with the site decomposition
`Ŝ_tot^- = ∑_x onSiteS x Ŝ^-` and the one-site action `onSiteS_mulVec_apply`; the surviving
matrix element `√((N−t)(t+1))` is absorbed into that site's own weight by `Math.sqrt_raise_coeff`,
leaving the factor `σ_x` whose site sum is `k + 1`.  The norm then follows from the `|Λ|`-fold
Vandermonde identity `Math.sum_prod_choose_fiber`.
-/

namespace LatticeSystem.Quantum

open _root_.Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## The ladder iterate in closed component form -/

/-- **Closed component form of the `k`-fold lowered highest-weight state.**  Applying
`(Ŝ_tot^-)^k` to the all-aligned state `Φ↑` produces a vector supported exactly on the
configurations of total lowering count `magSumS σ = k`, where its value is `k!` times the product
of the one-site Clebsch–Gordan weights `√(binom N σ_x)`.

Stated for a bare `k : ℕ`; it is unconditionally true, since for `k > |Λ| N` the fiber is empty
and both sides vanish.  The `Fin`-indexed `ladderIterateUp V N k` is definitionally the instance
at `k.val`.  This is the component form of the numerator of Tasaki, *Physics and Mathematics of
Quantum Many-Body Systems*, eq. (2.4.9), p. 33. -/
theorem totalSpinSOpMinus_pow_allAlignedStateS_zero_apply (k : ℕ) (σ : V → Fin (N + 1)) :
    ((totalSpinSOpMinus V N ^ k) *ᵥ allAlignedStateS V N 0) σ
      = if magSumS σ = k then
          (((k.factorial : ℝ) * ∏ x : V, Real.sqrt (N.choose (σ x).val) : ℝ) : ℂ)
        else 0 := by
  induction k generalizing σ with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec, allAlignedStateS, basisVecS_apply]
    by_cases h : magSumS σ = 0
    · have hval : ∀ x : V, (σ x).val = 0 := by
        intro x
        exact (Finset.sum_eq_zero_iff).mp h x (Finset.mem_univ x)
      have hσ : σ = allAlignedConfigS V N 0 := by
        funext x
        exact Fin.ext (by simpa [allAlignedConfigS] using hval x)
      have hprod : (∏ x : V, Real.sqrt (N.choose (σ x).val)) = 1 := by
        refine Finset.prod_eq_one fun x _ => ?_
        rw [hval x, Nat.choose_zero_right, Nat.cast_one, Real.sqrt_one]
      rw [if_pos hσ, if_pos h, hprod, Nat.factorial_zero]
      norm_num
    · have hσ : ¬ (σ = allAlignedConfigS V N 0) := by
        intro hc
        exact h (by rw [hc, magSumS_allAlignedConfigS]; simp)
      rw [if_neg hσ, if_neg h]
  | succ k ih =>
    have hstep : ((totalSpinSOpMinus V N ^ (k + 1)) *ᵥ allAlignedStateS V N 0) σ
        = ∑ x : V, ∑ c : Fin (N + 1), spinSOpMinus N (σ x) c
            * ((totalSpinSOpMinus V N ^ k) *ᵥ allAlignedStateS V N 0)
                (Function.update σ x c) := by
      rw [pow_succ', ← Matrix.mulVec_mulVec, totalSpinSOpMinus_def, Matrix.sum_mulVec,
        Finset.sum_apply]
      exact Finset.sum_congr rfl fun x _ => onSiteS_mulVec_apply x _ _ σ
    have hmagsplit : ∀ (x : V) (c : Fin (N + 1)),
        magSumS (Function.update σ x c)
          = c.val + ∑ y ∈ Finset.univ.erase x, (σ y).val := by
      intro x c
      rw [magSumS_def, ← Finset.add_sum_erase _ (fun y => ((Function.update σ x c) y).val)
        (Finset.mem_univ x), Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun y hy => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]
    have hprodsplit : ∀ (x : V) (c : Fin (N + 1)),
        (∏ y : V, Real.sqrt (N.choose ((Function.update σ x c) y).val))
          = Real.sqrt (N.choose c.val)
              * ∏ y ∈ Finset.univ.erase x, Real.sqrt (N.choose (σ y).val) := by
      intro x c
      rw [← Finset.mul_prod_erase _
        (fun y => Real.sqrt (N.choose ((Function.update σ x c) y).val))
        (Finset.mem_univ x), Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun y hy => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]
    have hmagσ : ∀ x : V,
        magSumS σ = (σ x).val + ∑ y ∈ Finset.univ.erase x, (σ y).val := by
      intro x
      rw [magSumS_def, ← Finset.add_sum_erase _ (fun y => (σ y).val) (Finset.mem_univ x)]
    have hprodσ : ∀ x : V, (∏ y : V, Real.sqrt (N.choose (σ y).val))
        = Real.sqrt (N.choose (σ x).val)
            * ∏ y ∈ Finset.univ.erase x, Real.sqrt (N.choose (σ y).val) := by
      intro x
      exact (Finset.mul_prod_erase _ _ (Finset.mem_univ x)).symm
    have hsite : ∀ x : V,
        (∑ c : Fin (N + 1), spinSOpMinus N (σ x) c
            * ((totalSpinSOpMinus V N ^ k) *ᵥ allAlignedStateS V N 0) (Function.update σ x c))
          = if magSumS σ = k + 1 then
              (((k.factorial : ℝ) * ((σ x).val : ℝ)
                * ∏ y : V, Real.sqrt (N.choose (σ y).val) : ℝ) : ℂ)
            else 0 := by
      intro x
      by_cases hzero : (σ x).val = 0
      · have hL : ∀ c : Fin (N + 1), spinSOpMinus N (σ x) c = 0 := by
          intro c
          exact spinSOpMinus_apply_other N (by omega)
        simp only [hL, zero_mul, Finset.sum_const_zero]
        by_cases hm : magSumS σ = k + 1
        · rw [if_pos hm, hzero]
          norm_num
        · rw [if_neg hm]
      · obtain ⟨t, ht⟩ : ∃ t, (σ x).val = t + 1 := ⟨(σ x).val - 1, by omega⟩
        have hxlt : (σ x).val < N + 1 := (σ x).isLt
        have htN : t < N := by omega
        set c₀ : Fin (N + 1) := ⟨t, by omega⟩ with hc₀
        have hc₀v : (c₀ : ℕ) = t := rfl
        rw [Finset.sum_eq_single c₀
          (fun c _ hc => by
            rw [spinSOpMinus_apply_other N (fun hcv => hc (Fin.ext (by omega))), zero_mul])
          (fun h => absurd (Finset.mem_univ _) h)]
        rw [spinSOpMinus_apply_lower N (show (c₀ : ℕ) + 1 = (σ x).val by rw [hc₀v, ht]),
          ih (Function.update σ x c₀), hmagsplit x c₀, hprodsplit x c₀]
        have hmx := hmagσ x
        rw [ht] at hmx
        by_cases hm : magSumS σ = k + 1
        · have hk : (c₀ : ℕ) + ∑ y ∈ Finset.univ.erase x, (σ y).val = k := by
            rw [hc₀v]; omega
          rw [if_pos hk, if_pos hm, hprodσ x, ← Complex.ofReal_mul]
          congr 1
          have hraise := Math.sqrt_raise_coeff (n := N) (t := t) htN
          have hsqrtarg : Real.sqrt (((N : ℝ) - ((c₀ : ℕ) : ℝ)) * (((c₀ : ℕ) : ℝ) + 1))
              = Real.sqrt (((t : ℝ) + 1) * ((N : ℝ) - ((t : ℝ) + 1) + 1)) := by
            rw [hc₀v]
            congr 1
            ring
          rw [hsqrtarg, hc₀v, ht]
          push_cast
          linear_combination ((k.factorial : ℝ)
            * ∏ y ∈ Finset.univ.erase x, Real.sqrt (N.choose (σ y).val)) * hraise
        · have hk : ¬ ((c₀ : ℕ) + ∑ y ∈ Finset.univ.erase x, (σ y).val = k) := by
            rw [hc₀v]; omega
          rw [if_neg hk, if_neg hm, mul_zero]
    rw [hstep, Finset.sum_congr rfl (fun x _ => hsite x)]
    by_cases hm : magSumS σ = k + 1
    · simp only [if_pos hm, ← Complex.ofReal_sum]
      congr 1
      have hsum : ∑ x : V, (((σ x).val : ℝ)) = ((k : ℝ) + 1) := by
        rw [← Nat.cast_sum, show (∑ x : V, (σ x).val) = k + 1 from hm]
        push_cast
        ring
      calc ∑ x : V, (k.factorial : ℝ) * ((σ x).val : ℝ)
              * ∏ y : V, Real.sqrt (N.choose (σ y).val)
          = ((k.factorial : ℝ) * ∏ y : V, Real.sqrt (N.choose (σ y).val))
              * ∑ x : V, ((σ x).val : ℝ) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by ring
        _ = ((k + 1).factorial : ℝ) * ∏ y : V, Real.sqrt (N.choose (σ y).val) := by
            rw [hsum, Nat.factorial_succ]
            push_cast
            ring
    · simp only [if_neg hm, Finset.sum_const_zero]

/-! ## The sector normalisation in closed form -/

/-- **Closed form of the sector normalisation** `‖(Ŝ_tot^-)^k Φ↑‖ = k! · √(binom (|Λ| N) k)`, the
denominator of Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, eq. (2.4.9), p. 33.

Squaring the closed component form leaves `(k!)²` times the fiber sum of `∏_x binom N σ_x`, which
the `|Λ|`-fold Vandermonde identity `Math.sum_prod_choose_fiber` evaluates to `binom (|Λ| N) k`.
No `[Nonempty V]` hypothesis is needed: for empty `V` both sides are `1`. -/
theorem saturatedLadderNorm_eq (k : Fin (Fintype.card V * N + 1)) :
    saturatedLadderNorm V N k
      = (k.val.factorial : ℝ) * Real.sqrt ((Fintype.card V * N).choose k.val) := by
  rw [saturatedLadderNorm, EuclideanSpace.norm_eq]
  have hterm : ∀ σ : V → Fin (N + 1),
      ‖(WithLp.toLp 2 (ladderIterateUp V N k) :
          EuclideanSpace ℂ (V → Fin (N + 1))).ofLp σ‖ ^ 2
        = if magSumS σ = k.val then
            ((k.val.factorial : ℝ) ^ 2 * ∏ x : V, (N.choose (σ x).val : ℝ)) else 0 := by
    intro σ
    rw [WithLp.ofLp_toLp, ladderIterateUp, totalSpinSOpMinus_pow_allAlignedStateS_zero_apply]
    by_cases h : magSumS σ = k.val
    · rw [if_pos h, if_pos h, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
        ← Finset.prod_pow]
      congr 1
      exact Finset.prod_congr rfl fun x _ => Real.sq_sqrt (Nat.cast_nonneg _)
    · rw [if_neg h, if_neg h, norm_zero]
      ring
  have hL0 : (∑ σ ∈ Finset.univ.filter (fun σ : V → Fin (N + 1) => magSumS σ = k.val),
      ∏ x : V, N.choose (σ x).val) = (Fintype.card V * N).choose k.val :=
    Math.sum_prod_choose_fiber V N k.val
  have hcast : (∑ σ ∈ Finset.univ.filter (fun σ : V → Fin (N + 1) => magSumS σ = k.val),
      ∏ x : V, (N.choose (σ x).val : ℝ)) = ((Fintype.card V * N).choose k.val : ℝ) := by
    rw [← hL0, Nat.cast_sum]
    exact Finset.sum_congr rfl fun σ _ => (Nat.cast_prod _ _).symm
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ), ← Finset.sum_filter, ← Finset.mul_sum, hcast,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

/-! ## The magnetisation-sector state in closed component form (eq. (2.4.11)) -/

/-- **Tasaki eq. (2.4.11)**, *Physics and Mathematics of Quantum Many-Body Systems*, p. 34, in its
general-`S` form: the normalised magnetisation-sector state `Φ_M` (`M = |Λ|S - k`) is supported on
the configurations of total lowering count `k`, where its value is the product of the one-site
Clebsch–Gordan weights `√(binom N σ_x)` divided by `√(binom (|Λ| N) k)`; the factorial `k!` of the
iterate and of its norm cancels.

For `S = 1/2` (`N = 1`) every one-site weight is `binom 1 σ_x = 1`, so the value is the constant
`(√(binom |Λ| k))⁻¹ = √[(S_max+M)!(S_max−M)!/(2S_max)!]` on the whole sector — the printed form of
(2.4.11), in which all configurations of the sector carry exactly the same weight. -/
theorem saturatedWeightVector_apply (k : Fin (Fintype.card V * N + 1)) (σ : V → Fin (N + 1)) :
    saturatedWeightVector V N k σ
      = if magSumS σ = k.val then
          (((Real.sqrt ((Fintype.card V * N).choose k.val))⁻¹
              * ∏ x : V, Real.sqrt (N.choose (σ x).val) : ℝ) : ℂ)
        else 0 := by
  have hchoose : (0 : ℝ) < Real.sqrt ((Fintype.card V * N).choose k.val) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp k.isLt))
  have hs : Real.sqrt ((Fintype.card V * N).choose k.val) ≠ 0 := ne_of_gt hchoose
  have hfac : (k.val.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [saturatedWeightVector, Pi.smul_apply, smul_eq_mul, saturatedLadderNorm_eq,
    ladderIterateUp, totalSpinSOpMinus_pow_allAlignedStateS_zero_apply]
  by_cases h : magSumS σ = k.val
  · rw [if_pos h, if_pos h, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    field_simp
  · rw [if_neg h, if_neg h, mul_zero]

end LatticeSystem.Quantum
