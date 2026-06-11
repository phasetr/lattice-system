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

omit [NormedAlgebra ℝ 𝔸] in
/-- **Telescoping power estimate.**  In a normed ring with `‖1‖ = 1`, if `‖C‖, ‖D‖ ≤ M` then
`‖Cⁿ − Dⁿ‖ ≤ n · M^(n−1) · ‖C − D‖`: telescope
`Cⁿ − Dⁿ = C·(Cⁿ⁻¹ − Dⁿ⁻¹) + (C − D)·Dⁿ⁻¹` and induct.  This converts the per-factor
closeness of the Trotter factors into closeness of their `n`-th powers. -/
theorem norm_pow_sub_pow_le [NormOneClass 𝔸] (C D : 𝔸) {M : ℝ} (hC : ‖C‖ ≤ M) (hD : ‖D‖ ≤ M) :
    ∀ n : ℕ, ‖C ^ n - D ^ n‖ ≤ (n : ℝ) * M ^ (n - 1) * ‖C - D‖
  | 0 => by simp
  | (n + 1) => by
    have hM0 : 0 ≤ M := le_trans (norm_nonneg C) hC
    have key : C ^ (n + 1) - D ^ (n + 1) = C * (C ^ n - D ^ n) + (C - D) * D ^ n := by
      rw [mul_sub, sub_mul, ← _root_.pow_succ', ← _root_.pow_succ']
      abel
    calc ‖C ^ (n + 1) - D ^ (n + 1)‖
        = ‖C * (C ^ n - D ^ n) + (C - D) * D ^ n‖ := by rw [key]
      _ ≤ ‖C * (C ^ n - D ^ n)‖ + ‖(C - D) * D ^ n‖ := norm_add_le _ _
      _ ≤ ‖C‖ * ‖C ^ n - D ^ n‖ + ‖C - D‖ * ‖D ^ n‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ M * ((n : ℝ) * M ^ (n - 1) * ‖C - D‖) + ‖C - D‖ * M ^ n := by
          refine add_le_add
            (mul_le_mul hC (norm_pow_sub_pow_le C D hC hD n) (norm_nonneg _) hM0) ?_
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (norm_pow_le D n).trans (pow_le_pow_left₀ (norm_nonneg D) hD n)
      _ ≤ ((n + 1 : ℕ) : ℝ) * M ^ ((n + 1) - 1) * ‖C - D‖ := by
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp
          · have hMM : M * M ^ (n - 1) = M ^ n := by
              have hn1 : n - 1 + 1 = n := by omega
              calc M * M ^ (n - 1) = M ^ (n - 1 + 1) := (_root_.pow_succ' M (n - 1)).symm
                _ = M ^ n := by rw [hn1]
            have heq : M * ((n : ℝ) * M ^ (n - 1) * ‖C - D‖) + ‖C - D‖ * M ^ n
                = ((n : ℝ) + 1) * M ^ n * ‖C - D‖ := by
              calc M * ((n : ℝ) * M ^ (n - 1) * ‖C - D‖) + ‖C - D‖ * M ^ n
                  = (n : ℝ) * (M * M ^ (n - 1)) * ‖C - D‖ + M ^ n * ‖C - D‖ := by ring
                _ = ((n : ℝ) + 1) * M ^ n * ‖C - D‖ := by rw [hMM]; ring
            rw [heq]
            push_cast
            simp

/-- **Trotter product comparison.**  For `0 ≤ s ≤ 1` the split product differs from the joint
exponential by `O(s²)`:
`‖e^{sA}e^{sB} − e^{s(A+B)}‖ ≤ 4 s² (‖A‖+‖B‖)² e^{‖A‖+‖B‖}`.
Both sides equal `1 + s(A+B)` to first order; the four second-order remainders — the two tails of
`e^{sA}e^{sB} − 1 − sA − sB`, the cross term `sA·(e^{sB}−1)`, and the tail of
`e^{s(A+B)} − 1 − s(A+B)` — are each bounded by `s²(‖A‖+‖B‖)²e^{‖A‖+‖B‖}` via the series tail
estimates. -/
theorem norm_exp_smul_mul_sub_exp_smul_add_le [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (A B : 𝔸) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖NormedSpace.exp (s • A) * NormedSpace.exp (s • B) - NormedSpace.exp (s • (A + B))‖
      ≤ 4 * s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by
  have ha : (0 : ℝ) ≤ ‖A‖ := norm_nonneg A
  have hb : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  have hEX : (0 : ℝ) < Real.exp (‖A‖ + ‖B‖) := Real.exp_pos _
  -- norms of the scaled elements
  have hsa : ‖s • A‖ = s * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hsb : ‖s • B‖ = s * ‖B‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hsab : ‖s • (A + B)‖ ≤ s * (‖A‖ + ‖B‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left (norm_add_le A B) hs0
  -- exponential comparisons (all `≤ e^{‖A‖+‖B‖}` since `s ≤ 1`)
  have hea : Real.exp (s * ‖A‖) ≤ Real.exp (‖A‖ + ‖B‖) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have heb : Real.exp (s * ‖B‖) ≤ Real.exp (‖A‖ + ‖B‖) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have heab : Real.exp (s * ‖A‖) * Real.exp (s * ‖B‖) ≤ Real.exp (‖A‖ + ‖B‖) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have heApB : Real.exp ‖s • (A + B)‖ ≤ Real.exp (‖A‖ + ‖B‖) :=
    Real.exp_le_exp.mpr (hsab.trans (by nlinarith))
  -- the four second-order remainders
  set F := NormedSpace.exp (s • A) * NormedSpace.exp (s • B) with hF
  set E := NormedSpace.exp (s • (A + B)) with hE
  -- algebraic split of `F − 1 − sA − sB`
  have key : F - 1 - (s • A + s • B)
      = (NormedSpace.exp (s • A) - 1 - s • A) * NormedSpace.exp (s • B)
        + (NormedSpace.exp (s • B) - 1 - s • B)
        + (s • A) * (NormedSpace.exp (s • B) - 1) := by
    rw [hF]
    generalize NormedSpace.exp (s • A) = P
    generalize NormedSpace.exp (s • B) = Q
    generalize s • A = X
    generalize s • B = Y
    rw [sub_mul, sub_mul, one_mul, mul_sub, mul_one]
    abel
  -- term bounds, each by `s²(‖A‖+‖B‖)² e^{‖A‖+‖B‖}`
  have hT1 : ‖(NormedSpace.exp (s • A) - 1 - s • A) * NormedSpace.exp (s • B)‖
      ≤ s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by
    calc ‖(NormedSpace.exp (s • A) - 1 - s • A) * NormedSpace.exp (s • B)‖
        ≤ ‖NormedSpace.exp (s • A) - 1 - s • A‖ * ‖NormedSpace.exp (s • B)‖ := norm_mul_le _ _
      _ ≤ (‖s • A‖ ^ 2 * Real.exp ‖s • A‖) * Real.exp ‖s • B‖ := by
          exact mul_le_mul (norm_exp_sub_one_sub_id_le (s • A)) (norm_exp_le_exp_norm (s • B))
            (norm_nonneg _) (by positivity)
      _ = s ^ 2 * ‖A‖ ^ 2 * (Real.exp (s * ‖A‖) * Real.exp (s * ‖B‖)) := by
          rw [hsa, hsb]; ring
      _ ≤ s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by
          gcongr
          nlinarith
  have hT2 : ‖NormedSpace.exp (s • B) - 1 - s • B‖
      ≤ s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by
    calc ‖NormedSpace.exp (s • B) - 1 - s • B‖
        ≤ ‖s • B‖ ^ 2 * Real.exp ‖s • B‖ := norm_exp_sub_one_sub_id_le (s • B)
      _ = s ^ 2 * ‖B‖ ^ 2 * Real.exp (s * ‖B‖) := by rw [hsb]; ring
      _ ≤ s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by
          gcongr
          nlinarith
  have hT3 : ‖(s • A) * (NormedSpace.exp (s • B) - 1)‖
      ≤ s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by
    calc ‖(s • A) * (NormedSpace.exp (s • B) - 1)‖
        ≤ ‖s • A‖ * ‖NormedSpace.exp (s • B) - 1‖ := norm_mul_le _ _
      _ ≤ (s * ‖A‖) * (‖s • B‖ * Real.exp ‖s • B‖) := by
          rw [hsa]
          exact mul_le_mul_of_nonneg_left (norm_exp_sub_one_le (s • B)) (by positivity)
      _ = s ^ 2 * (‖A‖ * ‖B‖) * Real.exp (s * ‖B‖) := by rw [hsb]; ring
      _ ≤ s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by
          gcongr
          nlinarith
  have hT4 : ‖E - 1 - s • (A + B)‖
      ≤ s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by
    calc ‖E - 1 - s • (A + B)‖
        ≤ ‖s • (A + B)‖ ^ 2 * Real.exp ‖s • (A + B)‖ := norm_exp_sub_one_sub_id_le _
      _ ≤ (s * (‖A‖ + ‖B‖)) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by
          exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hsab 2) heApB
            (Real.exp_pos _).le (by positivity)
      _ = s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by ring
  -- assemble: `F − E = (F − 1 − (sA+sB)) − (E − 1 − s(A+B))`
  have hFE : F - E = (F - 1 - (s • A + s • B)) - (E - 1 - s • (A + B)) := by
    rw [smul_add]; abel
  calc ‖F - E‖ = ‖(F - 1 - (s • A + s • B)) - (E - 1 - s • (A + B))‖ := by rw [hFE]
    _ ≤ ‖F - 1 - (s • A + s • B)‖ + ‖E - 1 - s • (A + B)‖ := norm_sub_le _ _
    _ ≤ (s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖)) * 3
        + s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by
        refine add_le_add ?_ hT4
        calc ‖F - 1 - (s • A + s • B)‖
            = ‖(NormedSpace.exp (s • A) - 1 - s • A) * NormedSpace.exp (s • B)
                + (NormedSpace.exp (s • B) - 1 - s • B)
                + (s • A) * (NormedSpace.exp (s • B) - 1)‖ := by rw [key]
          _ ≤ ‖(NormedSpace.exp (s • A) - 1 - s • A) * NormedSpace.exp (s • B)
                + (NormedSpace.exp (s • B) - 1 - s • B)‖
              + ‖(s • A) * (NormedSpace.exp (s • B) - 1)‖ := norm_add_le _ _
          _ ≤ ‖(NormedSpace.exp (s • A) - 1 - s • A) * NormedSpace.exp (s • B)‖
              + ‖NormedSpace.exp (s • B) - 1 - s • B‖
              + ‖(s • A) * (NormedSpace.exp (s • B) - 1)‖ := by
              exact add_le_add (norm_add_le _ _) le_rfl
          _ ≤ (s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖)) * 3 := by
              linarith [hT1, hT2, hT3]
    _ = 4 * s ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) := by ring


/-- **The Lie product (Trotter) formula in a complete normed `ℝ`-algebra.**
`e^{A+B} = lim_{n→∞} (e^{A/n} e^{B/n})^n`.  The joint exponential is *exactly* the `n`-th power
of its `1/n`-step (`exp_nsmul`), the per-step distance to the split product is `O(1/n²)`
(`norm_exp_smul_mul_sub_exp_smul_add_le`), the telescoping estimate (`norm_pow_sub_pow_le`)
multiplies that by `n·M^{n−1}` with `M = e^{(‖A‖+‖B‖)/n}` (so `M^{n−1} ≤ e^{‖A‖+‖B‖}`), and the
resulting `O(1/n)` bound squeezes to `0`. -/
theorem trotterProductFormula [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]
    (A B : 𝔸) :
    Tendsto
      (fun n : ℕ => (NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)) ^ n)
      atTop (𝓝 (NormedSpace.exp (A + B))) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm'
    (a := fun n : ℕ => (4 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) * Real.exp (‖A‖ + ‖B‖)) / n)
    ?_ (tendsto_const_div_atTop_nhds_zero_nat _)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hs1 : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
  have ha : (0 : ℝ) ≤ ‖A‖ := norm_nonneg A
  have hb : (0 : ℝ) ≤ ‖B‖ := norm_nonneg B
  -- the joint exponential is exactly the n-th power of its 1/n-step
  have hCn : NormedSpace.exp (A + B)
      = (NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))) ^ n := by
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0, one_smul]
  -- uniform per-factor norm bound `M = e^{(‖A‖+‖B‖)/n}`
  have hC : ‖NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))‖
      ≤ Real.exp ((n : ℝ)⁻¹ * (‖A‖ + ‖B‖)) :=
    (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_left (norm_add_le A B) hs0))
  have hD : ‖NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)‖
      ≤ Real.exp ((n : ℝ)⁻¹ * (‖A‖ + ‖B‖)) := by
    calc ‖NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)‖
        ≤ ‖NormedSpace.exp ((n : ℝ)⁻¹ • A)‖ * ‖NormedSpace.exp ((n : ℝ)⁻¹ • B)‖ :=
          norm_mul_le _ _
      _ ≤ Real.exp ‖(n : ℝ)⁻¹ • A‖ * Real.exp ‖(n : ℝ)⁻¹ • B‖ :=
          mul_le_mul (norm_exp_le_exp_norm _) (norm_exp_le_exp_norm _) (norm_nonneg _)
            (Real.exp_pos _).le
      _ = Real.exp (‖(n : ℝ)⁻¹ • A‖ + ‖(n : ℝ)⁻¹ • B‖) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((n : ℝ)⁻¹ * (‖A‖ + ‖B‖)) := by
          refine Real.exp_le_exp.mpr (le_of_eq ?_)
          rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
          ring
  -- M^{n−1} ≤ e^{‖A‖+‖B‖}
  have hMn : Real.exp ((n : ℝ)⁻¹ * (‖A‖ + ‖B‖)) ^ (n - 1) ≤ Real.exp (‖A‖ + ‖B‖) := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have h1n : (1 : ℕ) ≤ n := hn
      push_cast [h1n]
      ring
    rw [hcast]
    have hsub : ((n : ℝ) - 1) * (n : ℝ)⁻¹ = 1 - (n : ℝ)⁻¹ := by
      field_simp
    calc ((n : ℝ) - 1) * ((n : ℝ)⁻¹ * (‖A‖ + ‖B‖))
        = (1 - (n : ℝ)⁻¹) * (‖A‖ + ‖B‖) := by rw [← hsub]; ring
      _ ≤ 1 * (‖A‖ + ‖B‖) := by
          refine mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      _ = ‖A‖ + ‖B‖ := one_mul _
  -- assemble
  have htel := norm_pow_sub_pow_le
    (NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B))
    (NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))) hD hC n
  have hprod := norm_exp_smul_mul_sub_exp_smul_add_le A B hs0 hs1
  have hns : (n : ℝ) * ((n : ℝ)⁻¹) ^ 2 = 1 / n := by
    field_simp
  calc ‖(NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)) ^ n
        - NormedSpace.exp (A + B)‖
      = ‖(NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)) ^ n
        - (NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))) ^ n‖ := by rw [← hCn]
    _ ≤ (n : ℝ) * Real.exp ((n : ℝ)⁻¹ * (‖A‖ + ‖B‖)) ^ (n - 1)
        * ‖NormedSpace.exp ((n : ℝ)⁻¹ • A) * NormedSpace.exp ((n : ℝ)⁻¹ • B)
            - NormedSpace.exp ((n : ℝ)⁻¹ • (A + B))‖ := htel
    _ ≤ (n : ℝ) * Real.exp (‖A‖ + ‖B‖)
        * (4 * ((n : ℝ)⁻¹) ^ 2 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hMn (Nat.cast_nonneg n)) hprod
          (norm_nonneg _) (by positivity)
    _ = (4 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) * Real.exp (‖A‖ + ‖B‖))
        * ((n : ℝ) * ((n : ℝ)⁻¹) ^ 2) := by ring
    _ = (4 * (‖A‖ + ‖B‖) ^ 2 * Real.exp (‖A‖ + ‖B‖) * Real.exp (‖A‖ + ‖B‖)) / n := by
        rw [hns]
        ring

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
