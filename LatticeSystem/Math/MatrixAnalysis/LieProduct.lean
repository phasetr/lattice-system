import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Tasaki Appendix A.2.2: the Lie product formula (Theorem A.1)

The first numbered result of Tasaki's Mathematical Appendix.  For any (bounded) operators
`Â`, `B̂` — here finite complex matrices `Matrix n n ℂ`, the operator algebra of a
finite-volume quantum system — the exponential of a sum is the limit of symmetrically split
products:
`e^{Â+B̂} = lim_{N↑∞} (e^{Â/N} e^{B̂/N})^N`  (Tasaki eq. (A.2.21)).
Mathlib provides the *commuting* case (`Matrix.exp_add_of_commute`); the general
non-commuting Lie/Trotter formula for bounded operators is a standard but non-trivial
real-analysis result (Tasaki's footnote: "nineteenth century mathematics"), not currently in
mathlib.  Per the project's axiomatize-first policy it is recorded here as a documented axiom,
to be discharged later; it is not on the critical path of any Chapter-11 proof.

`NormedSpace.exp` is the matrix exponential used throughout the project (e.g. the Gibbs
exponential `e^{-βH}`); `(N : ℂ)⁻¹ • A = A/N`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.2.2, Theorem A.1, eq. (A.2.21), p. 465.
-/

namespace LatticeSystem.Math

open Filter Topology Nat

section ExpTailBounds

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- The exponential series with the first `k` terms dropped (index shift by `k`) remains
norm-summable: the tail of a norm-summable series is summable. -/
private theorem summable_norm_expSeries_shift (X : 𝔸) (k : ℕ) :
    Summable fun n : ℕ => ‖((n + k)!⁻¹ : ℝ) • X ^ (n + k)‖ :=
  (summable_nat_add_iff k).mpr (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X)

/-- Termwise comparison of the shifted exponential tail with the plain exponential series:
`‖(n+k)!⁻¹ • X^(n+k)‖ ≤ ‖X‖^k · (n!⁻¹‖X‖ⁿ)` (using `n! ≤ (n+k)!`). -/
private theorem norm_expSeries_shift_le (X : 𝔸) (k n : ℕ) (hk : 0 < k) :
    ‖((n + k)!⁻¹ : ℝ) • X ^ (n + k)‖ ≤ ‖X‖ ^ k * ((n !⁻¹ : ℝ) * ‖X‖ ^ n) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ((n + k)!⁻¹ : ℝ) * ‖X ^ (n + k)‖
      ≤ ((n + k)!⁻¹ : ℝ) * ‖X‖ ^ (n + k) := by
        gcongr
        exact norm_pow_le' X (by omega)
    _ ≤ (n !⁻¹ : ℝ) * ‖X‖ ^ (n + k) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        exact_mod_cast Nat.factorial_le (Nat.le_add_right n k)
    _ = ‖X‖ ^ k * ((n !⁻¹ : ℝ) * ‖X‖ ^ n) := by
        rw [pow_add]; ring

/-- The real exponential series sums to `Real.exp r`. -/
private theorem tsum_norm_series_eq_exp (r : ℝ) :
    ∑' n : ℕ, ((n !⁻¹ : ℝ) * r ^ n) = Real.exp r := by
  have h := congrFun (NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)) r
  rw [Real.exp_eq_exp_ℝ, h]
  simp [smul_eq_mul]

/-- The real exponential series is summable (comparison series for the tail bounds). -/
private theorem summable_norm_series (r : ℝ) (hr : 0 ≤ r) :
    Summable fun n : ℕ => ((n !⁻¹ : ℝ) * r ^ n) :=
  (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) r).congr
    (fun n => by
      rw [smul_eq_mul, Real.norm_eq_abs]
      exact abs_of_nonneg (by positivity))

/-- **Second-order tail bound for the exponential.**  In a complete normed `ℝ`-algebra,
`‖e^X − 1 − X‖ ≤ ‖X‖² e^{‖X‖}`: the difference is the `n ≥ 2` tail of the exponential series,
bounded termwise by `‖X‖²·(n!⁻¹‖X‖ⁿ)`.  This is the elementary estimate behind the Lie
product (Trotter) formula. -/
theorem norm_exp_sub_one_sub_id_le [CompleteSpace 𝔸] (X : 𝔸) :
    ‖NormedSpace.exp X - 1 - X‖ ≤ ‖X‖ ^ 2 * Real.exp ‖X‖ := by
  have hsum : Summable fun n : ℕ => (n !⁻¹ : ℝ) • X ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) X
  have h0 : NormedSpace.exp X = ∑' n : ℕ, (n !⁻¹ : ℝ) • X ^ n :=
    congrFun (NormedSpace.exp_eq_tsum ℝ) X
  -- split off the `n = 0` and `n = 1` terms
  have h1 : (∑' n : ℕ, (n !⁻¹ : ℝ) • X ^ n)
      = 1 + (X + ∑' n : ℕ, (((n + 2)!⁻¹ : ℝ) • X ^ (n + 2))) := by
    rw [hsum.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hsum).tsum_eq_zero_add]
    norm_num [Nat.factorial]
  have h2 : NormedSpace.exp X - 1 - X = ∑' n : ℕ, (((n + 2)!⁻¹ : ℝ) • X ^ (n + 2)) := by
    rw [h0, h1]; abel
  rw [h2]
  calc ‖∑' n : ℕ, (((n + 2)!⁻¹ : ℝ) • X ^ (n + 2))‖
      ≤ ∑' n : ℕ, ‖(((n + 2)!⁻¹ : ℝ) • X ^ (n + 2))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_expSeries_shift X 2)
    _ ≤ ∑' n : ℕ, ‖X‖ ^ 2 * ((n !⁻¹ : ℝ) * ‖X‖ ^ n) := by
        exact (summable_norm_expSeries_shift X 2).tsum_le_tsum
          (fun n => norm_expSeries_shift_le X 2 n (by omega))
          ((summable_norm_series ‖X‖ (norm_nonneg X)).mul_left (‖X‖ ^ 2))
    _ = ‖X‖ ^ 2 * Real.exp ‖X‖ := by
        rw [tsum_mul_left, tsum_norm_series_eq_exp]

/-- **First-order tail bound:** `‖e^X − 1‖ ≤ ‖X‖ e^{‖X‖}` (the `n ≥ 1` tail). -/
theorem norm_exp_sub_one_le [CompleteSpace 𝔸] (X : 𝔸) :
    ‖NormedSpace.exp X - 1‖ ≤ ‖X‖ * Real.exp ‖X‖ := by
  have hsum : Summable fun n : ℕ => (n !⁻¹ : ℝ) • X ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) X
  have h0 : NormedSpace.exp X = ∑' n : ℕ, (n !⁻¹ : ℝ) • X ^ n :=
    congrFun (NormedSpace.exp_eq_tsum ℝ) X
  have h1 : (∑' n : ℕ, (n !⁻¹ : ℝ) • X ^ n)
      = 1 + ∑' n : ℕ, (((n + 1)!⁻¹ : ℝ) • X ^ (n + 1)) := by
    rw [hsum.tsum_eq_zero_add]
    norm_num [Nat.factorial]
  have h2 : NormedSpace.exp X - 1 = ∑' n : ℕ, (((n + 1)!⁻¹ : ℝ) • X ^ (n + 1)) := by
    rw [h0, h1]; abel
  rw [h2]
  calc ‖∑' n : ℕ, (((n + 1)!⁻¹ : ℝ) • X ^ (n + 1))‖
      ≤ ∑' n : ℕ, ‖(((n + 1)!⁻¹ : ℝ) • X ^ (n + 1))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_expSeries_shift X 1)
    _ ≤ ∑' n : ℕ, ‖X‖ ^ 1 * ((n !⁻¹ : ℝ) * ‖X‖ ^ n) := by
        exact (summable_norm_expSeries_shift X 1).tsum_le_tsum
          (fun n => norm_expSeries_shift_le X 1 n (by omega))
          ((summable_norm_series ‖X‖ (norm_nonneg X)).mul_left (‖X‖ ^ 1))
    _ = ‖X‖ * Real.exp ‖X‖ := by
        rw [tsum_mul_left, tsum_norm_series_eq_exp, pow_one]

/-- **Norm bound for the exponential:** `‖e^X‖ ≤ e^{‖X‖}` (in a complete normed `ℝ`-algebra
with `‖1‖ = 1`). -/
theorem norm_exp_le_exp_norm [CompleteSpace 𝔸] [NormOneClass 𝔸] (X : 𝔸) :
    ‖NormedSpace.exp X‖ ≤ Real.exp ‖X‖ := by
  have h0 : NormedSpace.exp X = ∑' n : ℕ, (n !⁻¹ : ℝ) • X ^ n :=
    congrFun (NormedSpace.exp_eq_tsum ℝ) X
  rw [h0]
  calc ‖∑' n : ℕ, ((n !⁻¹ : ℝ) • X ^ n)‖
      ≤ ∑' n : ℕ, ‖((n !⁻¹ : ℝ) • X ^ n)‖ :=
        norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X)
    _ ≤ ∑' n : ℕ, ((n !⁻¹ : ℝ) * ‖X‖ ^ n) := by
        refine (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X).tsum_le_tsum
          (fun n => ?_) (summable_norm_series ‖X‖ (norm_nonneg X))
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        gcongr
        exact norm_pow_le X n
    _ = Real.exp ‖X‖ := tsum_norm_series_eq_exp ‖X‖

end ExpTailBounds

/-- **Tasaki Theorem A.1 (Lie product formula), AXIOM.**  For finite complex matrices `A`, `B`,
the exponential of the sum is the limit of the symmetric split product,
`e^{A+B} = lim_{N↑∞} (e^{A/N} e^{B/N})^N`.  Specializes to `Matrix.exp_add_of_commute` when
`A`, `B` commute; the general case is recorded as a documented axiom (standard analysis,
deferred). -/
axiom lieProductFormula {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n ℂ) :
    Tendsto
      (fun N : ℕ => (NormedSpace.exp ((N : ℂ)⁻¹ • A) * NormedSpace.exp ((N : ℂ)⁻¹ • B)) ^ N)
      atTop (𝓝 (NormedSpace.exp (A + B)))

end LatticeSystem.Math
