/-
Tasaki §4.2.2 Theorem 4.9 (the Tanaka state exhibits full symmetry breaking), arc PR4 — the axis-2
transverse fluctuation decay (4.2.15), `lim_{L↑∞} ⟨Ξ| (Ô_L^{(2)}/L^d)² |Ξ⟩ = 0`.

The mechanism (Tasaki eqs. (4.2.49)–(4.2.55), pp. 106–108).  Write `Ã := ô⁺ + ô⁻` (so
`Ô_L^{(1)} = (V/2) Ã`, `V = L^d`) and `P_k := ⟨Φ, p̂^k Φ⟩` (`phatMoment`).  The per-site transverse
fluctuation of the tower term `u_k` is
`δ_k := ⟨u_k| (ô^{(2)})² |u_k⟩ = ⟨tt_k, (Ô^{(2)})² tt_k⟩ / (B_k V²)`, `B_k = ‖(Ô_L^{(1)})^k Φ‖²`.
Since `(Ô^{(2)})² = V² p̂ − (Ô^{(1)})²` (`staggeredPhatS_eq_cartesian_sq`), `δ_k = Q_k − R_k` with
`Q_k = ⟨tt_k, p̂ tt_k⟩ / B_k = E_k / D_k` and `R_k = B_{k+1}/(B_k V²) = D_{k+1}/(4 D_k)`, where
`D_k := ⟨Φ, Ã^{2k} Φ⟩` and `E_k := ⟨Φ, Ã^k p̂ Ã^k Φ⟩`.

The two survive-and-count estimates are:
* **[F1]** `D_k = C(2k,k) P_k + O(1/V)` (this file): expand `Ã^{2k}` into words, drop unbalanced by
  charge selection, and pinch each of the `C(2k,k)` balanced words against `P_k` by the *fine*
  two-sided bound `orderWord_balanced_re_close_fine` (eq. (4.2.34)).  The genuinely `O(1/V)` band —
  not the crude `½ P_k` — is what makes the central-binomial cancellation visible.
* **[F2]** `E_k = C(2k,k) P_{k+1} + O(1/V)`: same expansion with a single charge-`0` `p̂`-insertion
  in the middle (length-`2(k+1)` balanced words), counted by Vandermonde's identity.

Combined with the Pascal ratio `(k+1) C(2k+2,k+1) = 2(2k+1) C(2k,k)`
(`Nat.succ_mul_centralBinom_succ`, eq. (4.2.43)) and the Rayleigh power ratio `P_{k+1} ≤ N² P_k`,
this gives `δ_k ≤ N²/(2k+2) + O(1/V) → 0`, whence `second2 = ½(δ_M + δ_{M+1}) → 0`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.33)/(4.2.34)/(4.2.49)–(4.2.55), pp. 104–108 (Tanaka [62]).
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaLowerBounds

namespace LatticeSystem.Quantum

open Matrix

/-! ### [F1] two-sided denominator closeness: `D_k = C(2k,k) P_k + O(1/V)` -/

/-- **[F1] Two-sided denominator closeness (eqs. (4.2.34)/(4.2.42)).**  On a `Ŝ_tot^{(3)}`-singlet
`Φ`, under the size condition `3 N (m+1)² ≤ 2 q₀ V`, the summed-density even denominator
`D_{m+1} = ⟨Φ, (ô⁺ + ô⁻)^{2(m+1)} Φ⟩` is within the genuinely `O(1/V)` band
`C(2(m+1),m+1) · (m+1)² (N/V) (3/2 P_m)` of `C(2(m+1),m+1) · P_{m+1}`.

Proof: expand `Ã^{2(m+1)}` into the `2^{2(m+1)}` order words; the singlet charge-selection rule
(`dotProduct_orderWord_singlet_eq_zero_of_charge_ne`) kills every unbalanced word, leaving the
`C(2(m+1),m+1)` balanced words (`card_ofFn_count_true_eq`), each pinched to within the fine band of
`P_{m+1}` by `orderWord_balanced_re_close_fine`.  Summing the per-word deviations and applying the
triangle inequality gives the stated bound.  This is the two-sided refinement of the one-sided
`orderSum_pow_two_denom_lower` used in Theorem 4.8. -/
theorem orderSum_pow_two_denom_close (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1) (m : ℕ)
    (hcond : 3 * (N : ℝ) * ((m : ℝ) + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    |(star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ (2 * (m + 1))).mulVec Φ).re
        - ((2 * (m + 1)).choose (m + 1) : ℝ) * phatMoment d L N Φ (m + 1)|
      ≤ ((2 * (m + 1)).choose (m + 1) : ℝ)
        * (((m : ℝ) + 1) ^ 2
          * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ m))) := by
  -- expand the summed density power into words and drop the unbalanced ones
  have hexp : (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
        + staggeredOrderDensityOpS d L N false) ^ (2 * (m + 1))).mulVec Φ).re
      = ∑ c ∈ Finset.univ.filter
          (fun c : Fin (2 * (m + 1)) → Bool => (List.ofFn c).count true = m + 1),
          (star Φ ⬝ᵥ (orderWordProd d L N (List.ofFn c)).mulVec Φ).re := by
    rw [orderDensitySum_pow_eq_sum_words, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun c : Fin (2 * (m + 1)) → Bool => (List.ofFn c).count true = m + 1)]
    have hunbal : ∑ c ∈ Finset.univ.filter
          (fun c : Fin (2 * (m + 1)) → Bool => ¬ (List.ofFn c).count true = m + 1),
          (star Φ ⬝ᵥ (orderWordProd d L N (List.ofFn c)).mulVec Φ).re = 0 := by
      refine Finset.sum_eq_zero (fun c hc => ?_)
      rw [Finset.mem_filter] at hc
      refine dotProduct_orderWord_singlet_eq_zero_of_charge_ne d L N Φ hsing _ ?_
      rw [mCharge_eq_count]
      intro hzero
      refine hc.2 ?_
      have hcount : (List.ofFn c).count true = (List.ofFn c).count false := by
        exact_mod_cast sub_eq_zero.mp hzero
      have hlen := count_true_add_count_false (List.ofFn c)
      rw [List.length_ofFn] at hlen
      omega
    rw [hunbal, add_zero]
  -- rewrite the constant term as a sum of `P_{m+1}` over the balanced words
  have hconst : ((2 * (m + 1)).choose (m + 1) : ℝ) * phatMoment d L N Φ (m + 1)
      = ∑ _c ∈ Finset.univ.filter
          (fun c : Fin (2 * (m + 1)) → Bool => (List.ofFn c).count true = m + 1),
          phatMoment d L N Φ (m + 1) := by
    rw [Finset.sum_const, card_ofFn_count_true_eq, nsmul_eq_mul]
  rw [hexp, hconst, ← Finset.sum_sub_distrib]
  -- the sum of per-word deviations is bounded termwise by the fine band
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hband : ∀ c ∈ Finset.univ.filter
      (fun c : Fin (2 * (m + 1)) → Bool => (List.ofFn c).count true = m + 1),
      |(star Φ ⬝ᵥ (orderWordProd d L N (List.ofFn c)).mulVec Φ).re - phatMoment d L N Φ (m + 1)|
        ≤ ((m : ℝ) + 1) ^ 2
          * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ m)) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    have hwt := hc.2
    have hwf : (List.ofFn c).count false = m + 1 := by
      have hlen := count_true_add_count_false (List.ofFn c)
      rw [List.length_ofFn, hwt] at hlen
      omega
    exact orderWord_balanced_re_close_fine d L N hN Φ hsing hm0 hlro m hcond
      (List.ofFn c) hwt hwf
  refine le_trans (Finset.sum_le_sum hband) ?_
  rw [Finset.sum_const, card_ofFn_count_true_eq, nsmul_eq_mul]

/-! ### [Gap2] the `p̂`-power ratio `P_{k+1} ≤ N² P_k` (eq. (4.2.33)) -/

/-- **`p̂` has operator norm `≤ N²`** (`= o₀²`, eq. (4.2.33)): `p̂ = ½(ô⁺ô⁻ + ô⁻ô⁺)` and each
per-volume order density has norm `≤ N` (`staggeredOrderDensityOpS_manyBodyOperatorNormS_le`), so by
the sub-multiplicative and triangle bounds `‖p̂‖ ≤ ½(N·N + N·N) = N²`. -/
theorem staggeredPhatS_manyBodyOperatorNormS_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N) :
    manyBodyOperatorNormS (staggeredPhatS d L N) ≤ (N : ℝ) ^ 2 := by
  rw [staggeredPhatS, manyBodyOperatorNormS_smul]
  have hc : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by rw [norm_inv]; norm_num
  have hmul : ∀ b b', manyBodyOperatorNormS
      (staggeredOrderDensityOpS d L N b * staggeredOrderDensityOpS d L N b')
        ≤ (N : ℝ) * (N : ℝ) := by
    intro b b'
    refine le_trans (manyBodyOperatorNormS_mul_le _ _) ?_
    exact mul_le_mul (staggeredOrderDensityOpS_manyBodyOperatorNormS_le d L N b hN)
      (staggeredOrderDensityOpS_manyBodyOperatorNormS_le d L N b' hN)
      (manyBodyOperatorNormS_nonneg _) (Nat.cast_nonneg N)
  have hadd := manyBodyOperatorNormS_add_le
    (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false)
    (staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)
  rw [hc]
  nlinarith [hadd, hmul true false, hmul false true, manyBodyOperatorNormS_nonneg
    (staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
      + staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true)]

/-- **Even-index Rayleigh bound**: `P_{2a+1} ≤ ‖p̂‖ · P_{2a}`.  Apply the operator Cauchy–Schwarz
corollary (`abs_re_dotProduct_mulVec_le_norm_mul` with `u = v = w = p̂^a Φ`) plus `le_abs_self`,
using the norm-square bridge `‖w‖₂² = ⟨w, w⟩` to turn the two `L²` norms into `⟨w, w⟩`; Hermiticity
of `p̂^a` collapses `⟨w, p̂ w⟩` to `P_{2a+1}` and `⟨w, w⟩` to `P_{2a}`. -/
private theorem phatMoment_two_mul_succ_le (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (a : ℕ) :
    phatMoment d L N Φ (2 * a + 1)
      ≤ manyBodyOperatorNormS (staggeredPhatS d L N) * phatMoment d L N Φ (2 * a) := by
  have hH := staggeredPhatS_isHermitian d L N
  have hnorm : ‖(WithLp.toLp 2 ((staggeredPhatS d L N ^ a).mulVec Φ)
        : EuclideanSpace ℂ (HypercubicTorus d L → Fin (N + 1)))‖ ^ 2
      = (star ((staggeredPhatS d L N ^ a).mulVec Φ)
          ⬝ᵥ (staggeredPhatS d L N ^ a).mulVec Φ).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp, dotProduct_comm,
      RCLike.re_to_complex]
  have hR : (star ((staggeredPhatS d L N ^ a).mulVec Φ)
          ⬝ᵥ (staggeredPhatS d L N).mulVec ((staggeredPhatS d L N ^ a).mulVec Φ)).re
      ≤ manyBodyOperatorNormS (staggeredPhatS d L N)
          * (star ((staggeredPhatS d L N ^ a).mulVec Φ)
              ⬝ᵥ (staggeredPhatS d L N ^ a).mulVec Φ).re := by
    calc (star ((staggeredPhatS d L N ^ a).mulVec Φ)
              ⬝ᵥ (staggeredPhatS d L N).mulVec ((staggeredPhatS d L N ^ a).mulVec Φ)).re
        ≤ |(star ((staggeredPhatS d L N ^ a).mulVec Φ)
              ⬝ᵥ (staggeredPhatS d L N).mulVec ((staggeredPhatS d L N ^ a).mulVec Φ)).re| :=
          le_abs_self _
      _ ≤ manyBodyOperatorNormS (staggeredPhatS d L N)
            * ‖(WithLp.toLp 2 ((staggeredPhatS d L N ^ a).mulVec Φ)
                : EuclideanSpace ℂ (HypercubicTorus d L → Fin (N + 1)))‖
            * ‖(WithLp.toLp 2 ((staggeredPhatS d L N ^ a).mulVec Φ)
                : EuclideanSpace ℂ (HypercubicTorus d L → Fin (N + 1)))‖ :=
          abs_re_dotProduct_mulVec_le_norm_mul (staggeredPhatS d L N) _ _
      _ = manyBodyOperatorNormS (staggeredPhatS d L N)
            * (star ((staggeredPhatS d L N ^ a).mulVec Φ)
                ⬝ᵥ (staggeredPhatS d L N ^ a).mulVec Φ).re := by
          rw [mul_assoc, ← pow_two, hnorm]
  have hww : (star ((staggeredPhatS d L N ^ a).mulVec Φ)
      ⬝ᵥ (staggeredPhatS d L N ^ a).mulVec Φ).re = phatMoment d L N Φ (2 * a) := by
    rw [hermitian_pow_dotProduct_split hH a a Φ, phatMoment, two_mul]
  have hpw : (star ((staggeredPhatS d L N ^ a).mulVec Φ)
      ⬝ᵥ (staggeredPhatS d L N).mulVec ((staggeredPhatS d L N ^ a).mulVec Φ)).re
      = phatMoment d L N Φ (2 * a + 1) := by
    rw [Matrix.mulVec_mulVec, ← pow_succ', hermitian_pow_dotProduct_split hH a (a + 1) Φ,
      phatMoment, show a + (a + 1) = 2 * a + 1 from by ring]
  rw [hpw, hww] at hR
  exact hR

/-- **Divide-out helper**: from `P₂² ≤ P₁ P₃`, `P₃ ≤ c P₂` with all data nonnegative, `P₂ ≤ c P₁`.
Pure real arithmetic (isolated from the heavy `phatMoment` terms so the search stays light). -/
private theorem le_of_sq_le_mul_ratio (P1 P2 P3 c : ℝ) (hc : 0 ≤ c)
    (hsq : P2 ^ 2 ≤ P1 * P3) (heven : P3 ≤ c * P2) (h1 : 0 ≤ P1) (h2 : 0 ≤ P2) :
    P2 ≤ c * P1 := by
  rcases eq_or_lt_of_le h2 with h0 | hpos
  · rw [← h0]; positivity
  · have hmul : P2 * P2 ≤ c * P1 * P2 := by nlinarith [hsq, heven, h1, h2]
    exact le_of_mul_le_mul_right hmul hpos

/-- **[Gap2] `p̂`-power ratio bound**: `P_{k+1} ≤ N² P_k` for every `k` (eq. (4.2.33) applied to
the moments).  Even `k` is the direct even-index Rayleigh bound; odd `k = 2a+1` combines the
log-convexity `P_{2a+2}² ≤ P_{2a+1} P_{2a+3}` (`phatMoment_sq_le`) with the even bound at `a+1`,
`P_{2a+3} ≤ ‖p̂‖ P_{2a+2}`, dividing out `P_{2a+2}`.  The operator norm `‖p̂‖ ≤ N²` closes both. -/
theorem phatMoment_succ_le_normSq (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (k : ℕ) :
    phatMoment d L N Φ (k + 1) ≤ (N : ℝ) ^ 2 * phatMoment d L N Φ k := by
  have hpn := staggeredPhatS_manyBodyOperatorNormS_le d L N hN
  have hpnnn : 0 ≤ manyBodyOperatorNormS (staggeredPhatS d L N) := manyBodyOperatorNormS_nonneg _
  rcases Nat.even_or_odd k with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · -- `k = a + a = 2a`
    have heven := phatMoment_two_mul_succ_le d L N Φ a
    rw [two_mul] at heven
    have hPnn : 0 ≤ phatMoment d L N Φ (a + a) := phatMoment_nonneg d L N Φ (a + a)
    calc phatMoment d L N Φ (a + a + 1)
        ≤ manyBodyOperatorNormS (staggeredPhatS d L N) * phatMoment d L N Φ (a + a) := heven
      _ ≤ (N : ℝ) ^ 2 * phatMoment d L N Φ (a + a) := mul_le_mul_of_nonneg_right hpn hPnn
  · -- `k = 2a + 1`
    have hP1nn := phatMoment_nonneg d L N Φ (2 * a + 1)
    have hkey : phatMoment d L N Φ (2 * a + 1 + 1)
        ≤ manyBodyOperatorNormS (staggeredPhatS d L N) * phatMoment d L N Φ (2 * a + 1) :=
      le_of_sq_le_mul_ratio _ _ _ _ hpnnn (phatMoment_sq_le d L N Φ (2 * a + 1))
        (by
          have h := phatMoment_two_mul_succ_le d L N Φ (a + 1)
          rwa [show 2 * (a + 1) + 1 = 2 * a + 1 + 2 from by ring,
            show 2 * (a + 1) = 2 * a + 1 + 1 from by ring] at h)
        hP1nn (phatMoment_nonneg d L N Φ (2 * a + 1 + 1))
    calc phatMoment d L N Φ (2 * a + 1 + 1)
        ≤ manyBodyOperatorNormS (staggeredPhatS d L N) * phatMoment d L N Φ (2 * a + 1) := hkey
      _ ≤ (N : ℝ) ^ 2 * phatMoment d L N Φ (2 * a + 1) := mul_le_mul_of_nonneg_right hpn hP1nn

/-! ### [F2] two-sided `p̂`-insertion closeness: `E_k = C(2k,k) P_{k+1} + O(1/V)` -/

/-- **Balanced-pair count**: the number of pairs `(cₗ, cᵣ)` of length-`k` binary words with combined
`true`-count `k` equals the central binomial `C(2k, k)`.  The concatenation bijection
`(cₗ, cᵣ) ↦ Fin.append cₗ cᵣ` (`List.ofFn_fin_append` + `List.count_append`) reduces it to the
single-word count `card_ofFn_count_true_eq` at length `2k`. -/
theorem card_prod_count_true_add (k : ℕ) :
    (Finset.univ.filter (fun p : (Fin k → Bool) × (Fin k → Bool) =>
        (List.ofFn p.1).count true + (List.ofFn p.2).count true = k)).card = (2 * k).choose k := by
  rw [two_mul, ← card_ofFn_count_true_eq (k + k) k]
  refine Finset.card_nbij' (fun p => Fin.append p.1 p.2)
    (fun c => (fun i => c (Fin.castAdd k i), fun i => c (Fin.natAdd k i))) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hp
    rw [Finset.coe_filter, Set.mem_setOf_eq]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [List.ofFn_fin_append, List.count_append]
    exact hp.2
  · intro c hc
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hc
    rw [Finset.coe_filter, Set.mem_setOf_eq]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsplit : (List.ofFn c).count true
        = (List.ofFn (fun i => c (Fin.castAdd k i))).count true
          + (List.ofFn (fun i => c (Fin.natAdd k i))).count true := by
      rw [← List.count_append, ← List.ofFn_fin_append, Fin.append_castAdd_natAdd]
    rw [← hsplit]; exact hc.2
  · intro p _
    refine Prod.ext ?_ ?_ <;> funext i
    · exact Fin.append_left p.1 p.2 i
    · exact Fin.append_right p.1 p.2 i
  · intro c _
    exact Fin.append_castAdd_natAdd

/-- **`p̂`-insertion sandwich as a word double sum**: expanding `Ã = ô⁺ + ô⁻` on both sides,
`⟨Φ, Ã^k G Ã^k Φ⟩` (for a fixed middle word operator `G = orderWordProd mid`) is the double sum over
`(cₗ, cᵣ)` of the real expectations of the concatenated words `cₗ ++ mid ++ cᵣ`
(`orderDensitySum_pow_eq_sum_words` + `orderWordProd_append`). -/
private theorem orderSum_pow_sandwich_re_eq (d L N k : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (mid : List Bool) :
    (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ k
        * orderWordProd d L N mid
        * (staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ).re
      = ∑ cl : Fin k → Bool, ∑ cr : Fin k → Bool,
          (star Φ ⬝ᵥ (orderWordProd d L N (List.ofFn cl ++ mid ++ List.ofFn cr)).mulVec Φ).re := by
  have hop : (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ k
        * orderWordProd d L N mid
        * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ k
      = ∑ cl : Fin k → Bool, ∑ cr : Fin k → Bool,
          orderWordProd d L N (List.ofFn cl ++ mid ++ List.ofFn cr) := by
    rw [orderDensitySum_pow_eq_sum_words, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun cl _ => ?_)
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl (fun cr _ => ?_)
    rw [orderWordProd_append, orderWordProd_append]
  rw [hop, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun cl _ => ?_)
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]

/-- **Per-mid `p̂`-insertion closeness**: for a charge-`0` middle word `mid` (one `true`, one
`false`), the sandwiched expectation `⟨Φ, Ã^k (orderWordProd mid) Ã^k Φ⟩` is within
`C(2k,k) · (k+1)² (N/V) (3/2 P_k)` of `C(2k,k) · P_{k+1}`.  The concatenated words `cₗ ++ mid ++ cᵣ`
have length `2(k+1)`; charge selection kills the pairs with `#t(cₗ)+#t(cᵣ) ≠ k`, and the surviving
`C(2k,k)` balanced pairs (`card_prod_count_true_add`) are each pinched by the fine band. -/
private theorem orderSum_pow_mid_close (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1) (k : ℕ)
    (hcond : 3 * (N : ℝ) * ((k : ℝ) + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (mid : List Bool) (hmt : mid.count true = 1) (hmf : mid.count false = 1) :
    |(star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ k
          * orderWordProd d L N mid
          * (staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ).re
        - ((2 * k).choose k : ℝ) * phatMoment d L N Φ (k + 1)|
      ≤ ((2 * k).choose k : ℝ)
        * (((k : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ k))) := by
  rw [orderSum_pow_sandwich_re_eq,
    show (∑ cl : Fin k → Bool, ∑ cr : Fin k → Bool,
          (star Φ ⬝ᵥ (orderWordProd d L N (List.ofFn cl ++ mid ++ List.ofFn cr)).mulVec Φ).re)
        = ∑ p : (Fin k → Bool) × (Fin k → Bool),
            (star Φ ⬝ᵥ (orderWordProd d L N (List.ofFn p.1 ++ mid ++ List.ofFn p.2)).mulVec Φ).re
      from by rw [Fintype.sum_prod_type]]
  -- helper counts on the concatenated word
  have hcount : ∀ p : (Fin k → Bool) × (Fin k → Bool),
      (List.ofFn p.1 ++ mid ++ List.ofFn p.2).count true
          = (List.ofFn p.1).count true + 1 + (List.ofFn p.2).count true
        ∧ (List.ofFn p.1 ++ mid ++ List.ofFn p.2).count false
          = (List.ofFn p.1).count false + 1 + (List.ofFn p.2).count false := by
    intro p
    constructor <;> rw [List.count_append, List.count_append]
    · rw [hmt]
    · rw [hmf]
  have hlen : ∀ p : (Fin k → Bool) × (Fin k → Bool),
      (List.ofFn p.1).count true + (List.ofFn p.1).count false = k
        ∧ (List.ofFn p.2).count true + (List.ofFn p.2).count false = k := by
    intro p
    refine ⟨?_, ?_⟩ <;>
      · have := count_true_add_count_false (List.ofFn (Prod.fst p))
        have := count_true_add_count_false (List.ofFn (Prod.snd p))
        simp only [List.length_ofFn] at *; omega
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : (Fin k → Bool) × (Fin k → Bool) =>
      (List.ofFn p.1).count true + (List.ofFn p.2).count true = k)]
  -- unbalanced pairs carry nonzero charge, so vanish
  have hunbal : ∑ p ∈ Finset.univ.filter
        (fun p : (Fin k → Bool) × (Fin k → Bool) =>
          ¬ (List.ofFn p.1).count true + (List.ofFn p.2).count true = k),
        (star Φ ⬝ᵥ (orderWordProd d L N
          (List.ofFn p.1 ++ mid ++ List.ofFn p.2)).mulVec Φ).re = 0 := by
    refine Finset.sum_eq_zero (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    refine dotProduct_orderWord_singlet_eq_zero_of_charge_ne d L N Φ hsing _ ?_
    rw [mCharge_eq_count, (hcount p).1, (hcount p).2]
    intro hzero
    refine hp.2 ?_
    have hnat : (List.ofFn p.1).count true + 1 + (List.ofFn p.2).count true
        = (List.ofFn p.1).count false + 1 + (List.ofFn p.2).count false := by
      exact_mod_cast sub_eq_zero.mp hzero
    have h1 := (hlen p).1
    have h2 := (hlen p).2
    omega
  rw [hunbal, add_zero]
  -- constant term as a balanced-pair sum of `P_{k+1}`
  have hconst : ((2 * k).choose k : ℝ) * phatMoment d L N Φ (k + 1)
      = ∑ _p ∈ Finset.univ.filter
          (fun p : (Fin k → Bool) × (Fin k → Bool) =>
            (List.ofFn p.1).count true + (List.ofFn p.2).count true = k),
          phatMoment d L N Φ (k + 1) := by
    rw [Finset.sum_const, card_prod_count_true_add, nsmul_eq_mul]
  rw [hconst, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hband : ∀ p ∈ Finset.univ.filter
      (fun p : (Fin k → Bool) × (Fin k → Bool) =>
        (List.ofFn p.1).count true + (List.ofFn p.2).count true = k),
      |(star Φ ⬝ᵥ (orderWordProd d L N
            (List.ofFn p.1 ++ mid ++ List.ofFn p.2)).mulVec Φ).re - phatMoment d L N Φ (k + 1)|
        ≤ ((k : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ k)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hbal := hp.2
    have hwt : (List.ofFn p.1 ++ mid ++ List.ofFn p.2).count true = k + 1 := by
      rw [(hcount p).1]; omega
    have hwf : (List.ofFn p.1 ++ mid ++ List.ofFn p.2).count false = k + 1 := by
      rw [(hcount p).2]
      have h1 := (hlen p).1
      have h2 := (hlen p).2
      omega
    exact orderWord_balanced_re_close_fine d L N hN Φ hsing hm0 hlro k hcond _ hwt hwf
  refine le_trans (Finset.sum_le_sum hband) ?_
  rw [Finset.sum_const, card_prod_count_true_add, nsmul_eq_mul]

/-- **[F2] Two-sided `p̂`-insertion closeness (eq. (4.2.50)).**  On a `Ŝ_tot^{(3)}`-singlet, under
`3 N (k+1)² ≤ 2 q₀ V`, the `p̂`-sandwich `E_k = ⟨Φ, Ã^k p̂ Ã^k Φ⟩` is within
`C(2k,k) · (k+1)² (N/V) (3/2 P_k)` of `C(2k,k) · P_{k+1}`.  Writing `p̂ = ½(ô⁺ô⁻ + ô⁻ô⁺)`, both
charge-`0` middle words `[t,f]` and `[f,t]` are handled by `orderSum_pow_mid_close`, and the two
closeness bounds combine through the `½`-average. -/
theorem orderSum_pow_phat_insert_close (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1) (k : ℕ)
    (hcond : 3 * (N : ℝ) * ((k : ℝ) + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    |(star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ k
          * staggeredPhatS d L N
          * (staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ).re
        - ((2 * k).choose k : ℝ) * phatMoment d L N Φ (k + 1)|
      ≤ ((2 * k).choose k : ℝ)
        * (((k : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ k))) := by
  have htf : staggeredOrderDensityOpS d L N true * staggeredOrderDensityOpS d L N false
      = orderWordProd d L N [true, false] := by simp [orderWordProd]
  have hft : staggeredOrderDensityOpS d L N false * staggeredOrderDensityOpS d L N true
      = orderWordProd d L N [false, true] := by simp [orderWordProd]
  -- expand `p̂ = ½(ô⁺ô⁻ + ô⁻ô⁺)` and average the two charge-`0` sandwiches
  have hopid : (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ k
        * staggeredPhatS d L N
        * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ k
      = (2 : ℂ)⁻¹ •
          ((staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ k
              * orderWordProd d L N [true, false]
              * (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ k
            + (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false) ^ k
              * orderWordProd d L N [false, true]
              * (staggeredOrderDensityOpS d L N true
                + staggeredOrderDensityOpS d L N false) ^ k) := by
    rw [staggeredPhatS, htf, hft, mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_add, add_mul]
  have hexp : (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ k * staggeredPhatS d L N
          * (staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ).re
      = 1 / 2 * ((star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ k * orderWordProd d L N [true, false]
            * (staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ).re
          + (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ k * orderWordProd d L N [false, true]
            * (staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ).re) := by
    rw [hopid, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.add_mulVec, dotProduct_add,
      show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) from by norm_num, Complex.re_ofReal_mul, Complex.add_re]
  rw [hexp]
  have hbtf := orderSum_pow_mid_close d L N hN Φ hsing hm0 hlro k hcond [true, false]
    (by decide) (by decide)
  have hbft := orderSum_pow_mid_close d L N hN Φ hsing hm0 hlro k hcond [false, true]
    (by decide) (by decide)
  rw [show (1 / 2 * ((star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ k * orderWordProd d L N [true, false]
          * (staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ).re
        + (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ k * orderWordProd d L N [false, true]
          * (staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ).re)
      - ((2 * k).choose k : ℝ) * phatMoment d L N Φ (k + 1))
      = 1 / 2 * (((star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ k * orderWordProd d L N [true, false]
            * (staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ).re
          - ((2 * k).choose k : ℝ) * phatMoment d L N Φ (k + 1))
        + ((star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ k * orderWordProd d L N [false, true]
            * (staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ).re
          - ((2 * k).choose k : ℝ) * phatMoment d L N Φ (k + 1))) from by ring, abs_mul,
    show |(1 : ℝ) / 2| = 1 / 2 from by norm_num]
  refine le_trans (mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)) ?_
  linarith [hbtf, hbft]

/-! ### [F4] `Ô^{(2)}`-infrastructure: Hermiticity and parity commutation of `(Ô^{(2)})²` -/

/-- **The `2`-axis staggered order operator is Hermitian** (mirror of
`staggeredOrderOp1S_isHermitian`, using `spinSOp2_isHermitian`). -/
theorem staggeredOrderOp2S_isHermitian {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (A : Λ → Bool) (N : ℕ) : (staggeredOrderOp2S A N).IsHermitian := by
  refine Matrix.isHermitian_sum Finset.univ (fun x _ => ?_)
  refine Matrix.IsHermitian.smul ?_ ?_
  · exact onSiteS_isHermitian x (spinSOp2_isHermitian N)
  · by_cases h : A x
    · simp [h, IsSelfAdjoint, star_one]
    · simp [h, IsSelfAdjoint]

/-- `Û Ô^{(2)} = -Ô^{(2)} Û`: the parity operator anticommutes with the `2`-axis order operator
(both raising and lowering flip sign under `Û`, so does their difference `2i Ô^{(2)}`). -/
private theorem diagonal_magParitySignS_mul_staggeredOrderOp2S {Λ : Type*} [Fintype Λ]
    [DecidableEq Λ] {N : ℕ} (A : Λ → Bool) :
    Matrix.diagonal (magParitySignS (Λ := Λ) (N := N)) * staggeredOrderOp2S A N
      = -(staggeredOrderOp2S A N * Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))) := by
  have key : Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))
        * (staggeredRaisingOpS A N - staggeredLoweringOpS A N)
      = -((staggeredRaisingOpS A N - staggeredLoweringOpS A N)
        * Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, diagonal_magParitySignS_mul_staggeredRaisingOpS,
      diagonal_magParitySignS_mul_staggeredLoweringOpS]
    abel
  rw [staggeredOrderOp2S_eq_smul, mul_smul_comm, key, smul_neg, smul_mul_assoc]

/-- **`(Ô^{(2)})²` commutes with the parity operator** `Û = diag(magParitySignS)` (two
anticommutations), the `2`-axis analogue of `staggeredOrderOp1S_sq_comm_diagonal_magParitySignS`. -/
private theorem staggeredOrderOp2S_sq_comm_diagonal_magParitySignS {Λ : Type*} [Fintype Λ]
    [DecidableEq Λ] {N : ℕ} (A : Λ → Bool) :
    (staggeredOrderOp2S A N * staggeredOrderOp2S A N)
        * Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))
      = Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))
        * (staggeredOrderOp2S A N * staggeredOrderOp2S A N) := by
  have hDH := diagonal_magParitySignS_mul_staggeredOrderOp2S (Λ := Λ) (N := N) A
  set H := staggeredOrderOp2S A N
  set D := Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))
  have hHD : H * D = -(D * H) := by rw [hDH]; exact (neg_neg _).symm
  calc H * H * D = H * (H * D) := mul_assoc H H D
    _ = H * -(D * H) := by rw [hHD]
    _ = -(H * (D * H)) := by rw [mul_neg]
    _ = -(H * D * H) := by rw [mul_assoc]
    _ = -(-(D * H) * H) := by rw [hHD]
    _ = D * H * H := by rw [neg_mul]; exact neg_neg _
    _ = D * (H * H) := mul_assoc D H H

/-- **`(Ô^{(2)})²` diagonal element**: `⟨û_j, (Ô^{(2)})² û_j⟩.re = ⟨tt_j, (Ô^{(2)})² tt_j⟩.re / B_j`
for `B_j = ‖tt_j‖² > 0` (the unit normalization contributes `B_j⁻¹`). -/
private theorem staggeredOrderOp2Ssq_unitNormalize_diag {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {N : ℕ} (A : Λ → Bool) (j : ℕ) {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hj : 0 < vecNormSqRe (tanakaTowerTerm A N j Φ)) :
    (star (unitNormalize (tanakaTowerTerm A N j Φ))
        ⬝ᵥ (staggeredOrderOp2S A N * staggeredOrderOp2S A N).mulVec
          (unitNormalize (tanakaTowerTerm A N j Φ))).re
      = (star (tanakaTowerTerm A N j Φ)
          ⬝ᵥ (staggeredOrderOp2S A N * staggeredOrderOp2S A N).mulVec
            (tanakaTowerTerm A N j Φ)).re / vecNormSqRe (tanakaTowerTerm A N j Φ) := by
  simp only [unitNormalize]
  rw [star_smul_dotProduct_mulVec_smul]
  have hc : star (((Real.sqrt (vecNormSqRe (tanakaTowerTerm A N j Φ)) : ℝ) : ℂ)⁻¹)
        * ((Real.sqrt (vecNormSqRe (tanakaTowerTerm A N j Φ)) : ℝ) : ℂ)⁻¹
      = (((vecNormSqRe (tanakaTowerTerm A N j Φ))⁻¹ : ℝ) : ℂ) := by
    rw [Complex.star_def, map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hj.le, ← Complex.ofReal_inv]
  rw [hc, Complex.re_ofReal_mul, mul_comm, ← div_eq_mul_inv]

/-! ### [F4] `second2` decomposition into the two transverse fluctuations `δ_M`, `δ_{M+1}` -/

/-- **[F4] `second2` sandwich decomposition (eq. (4.2.49)).**  The axis-2 squared per-site moment of
the Tanaka state decomposes into the average of the two diagonal transverse fluctuations
`δ_k = ⟨tt_k, (Ô^{(2)})² tt_k⟩ / (B_k V²)`: `second2 = ½(δ_M + δ_{M+1})`.  The squared order
operator is Hermitian and conserves parity, so the cross term vanishes
(`tanakaTowerTerm_cross_charge_conserving_eq_zero`); the diagonal terms are the normalized
fluctuations. -/
theorem tanakaOrderSecond2_eq_half_sum (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hBM : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ))
    (hBM1 : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)) :
    tanakaOrderSecond2 d L N M Φ
      = 1 / 2 * ((star (tanakaTowerTerm (torusParitySublattice d L) N M Φ)
            ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
              * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec
              (tanakaTowerTerm (torusParitySublattice d L) N M Φ)).re
            / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ)
          + (star (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)
            ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
              * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec
              (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)).re
            / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ))
        / ((L : ℝ) ^ d) ^ 2 := by
  have hHHh : (staggeredOrderOp2S (torusParitySublattice d L) N
      * staggeredOrderOp2S (torusParitySublattice d L) N).IsHermitian :=
    (staggeredOrderOp2S_isHermitian _ _).mul_of_commute (staggeredOrderOp2S_isHermitian _ _) rfl
  have hden : vecNormSqRe (tanakaSSBState (torusParitySublattice d L) N M Φ) = 1 :=
    tanakaSSBState_vecNormSqRe_eq_one _ M hsing3 hBM hBM1
  have hcross0 : star (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N M Φ))
      ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
        * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec
        (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)) = 0 := by
    simp only [unitNormalize]
    rw [star_smul_dotProduct_mulVec_smul,
      tanakaTowerTerm_cross_charge_conserving_eq_zero (torusParitySublattice d L) _ M hsing3
        (staggeredOrderOp2S_sq_comm_diagonal_magParitySignS (torusParitySublattice d L)),
      mul_zero]
  have hnum : (star (tanakaSSBState (torusParitySublattice d L) N M Φ)
      ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
        * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec
        (tanakaSSBState (torusParitySublattice d L) N M Φ)).re
      = 1 / 2 * ((star (tanakaTowerTerm (torusParitySublattice d L) N M Φ)
            ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
              * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec
              (tanakaTowerTerm (torusParitySublattice d L) N M Φ)).re
            / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ)
          + (star (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)
            ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
              * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec
              (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)).re
            / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)) := by
    rw [tanakaSSBState_dotProduct_mulVec_re_eq (torusParitySublattice d L) M
        (staggeredOrderOp2S (torusParitySublattice d L) N
          * staggeredOrderOp2S (torusParitySublattice d L) N) hHHh Φ,
      staggeredOrderOp2Ssq_unitNormalize_diag (torusParitySublattice d L) M hBM,
      staggeredOrderOp2Ssq_unitNormalize_diag (torusParitySublattice d L) (M + 1) hBM1,
      hcross0, Complex.zero_re, add_zero]
  rw [tanakaOrderSecond2, expectationRatioRe, hnum,
    show (star (tanakaSSBState (torusParitySublattice d L) N M Φ)
      ⬝ᵥ tanakaSSBState (torusParitySublattice d L) N M Φ).re = 1 from hden, div_one]

/-! ### [F3] the transverse fluctuation `δ_k = (4 E_k − D_{k+1}) / (4 D_k)` -/

/-- **[F3] Bridge: the transverse fluctuation as a `D`/`E` ratio.**  Writing `Ã = ô⁺ + ô⁻` and
`D_j = ⟨Φ, Ã^{2j} Φ⟩`, `E_k = ⟨Φ, Ã^k p̂ Ã^k Φ⟩`, the per-site diagonal transverse fluctuation
`δ_k = ⟨tt_k, (Ô^{(2)})² tt_k⟩ / (B_k V²)` equals `(4 E_k − D_{k+1}) / (4 D_k)`.  Uses the scale
invariance `tt_k = (V/2)^k Ã^k Φ`, the Cartesian identity `(Ô^{(2)})² = V² p̂ − (Ô^{(1)})²`, and
`(Ô^{(1)})² = (V²/4) Ã²`; the volume factors `V` and `(V/2)^{2k}` cancel in the ratio. -/
theorem tanaka_delta_eq (d L N k : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    (star (tanakaTowerTerm (torusParitySublattice d L) N k Φ)
        ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
          * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec
          (tanakaTowerTerm (torusParitySublattice d L) N k Φ)).re
        / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N k Φ) / ((L : ℝ) ^ d) ^ 2
      = (4 * (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ k * staggeredPhatS d L N
            * (staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ k).mulVec Φ).re
          - (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
              + staggeredOrderDensityOpS d L N false) ^ (2 * (k + 1))).mulVec Φ).re)
        / (4 * (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
            + staggeredOrderDensityOpS d L N false) ^ (2 * k)).mulVec Φ).re) := by
  set Ã := staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false with hÃ
  have hÃH : Ã.IsHermitian := orderDensitySum_isHermitian d L N
  have hVne : ((L : ℂ) ^ d) ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne L))
  have hVRne : ((L : ℝ) ^ d) ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne L))
  -- scale invariance: replace `tt_k` by `Ã^k Φ`
  have htt : tanakaTowerTerm (torusParitySublattice d L) N k Φ
      = ((L : ℂ) ^ d / 2) ^ k • (Ã ^ k).mulVec Φ := by
    rw [tanakaTowerTerm, staggeredOrderOp1S_eq_smul_orderDensitySum, smul_pow, Matrix.smul_mulVec]
  have hc : ((L : ℂ) ^ d / 2) ^ k ≠ 0 :=
    pow_ne_zero _ (div_ne_zero hVne two_ne_zero)
  have hscale : (star (tanakaTowerTerm (torusParitySublattice d L) N k Φ)
        ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
          * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec
          (tanakaTowerTerm (torusParitySublattice d L) N k Φ)).re
        / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N k Φ)
      = (star ((Ã ^ k).mulVec Φ)
          ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
            * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec ((Ã ^ k).mulVec Φ)).re
        / (star ((Ã ^ k).mulVec Φ) ⬝ᵥ (Ã ^ k).mulVec Φ).re := by
    rw [vecNormSqRe, htt]
    exact rayleigh_smul_invariant _ _ hc _
  rw [hscale]
  -- the sandwiched middle operator: `(Ô²)² = V² p̂ − (V²/4) Ã²`
  have hmid : star ((Ã ^ k).mulVec Φ)
        ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
          * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec ((Ã ^ k).mulVec Φ)
      = ((L : ℂ) ^ d) ^ 2 * (star Φ ⬝ᵥ (Ã ^ k * staggeredPhatS d L N * Ã ^ k).mulVec Φ)
        - ((L : ℂ) ^ d) ^ 2 / 4
          * (star Φ ⬝ᵥ (Ã ^ (2 * (k + 1))).mulVec Φ) := by
    have hV2 : ((L : ℂ) ^ d) ^ 2 • staggeredPhatS d L N
        = staggeredOrderOp1S (torusParitySublattice d L) N
            * staggeredOrderOp1S (torusParitySublattice d L) N
          + staggeredOrderOp2S (torusParitySublattice d L) N
            * staggeredOrderOp2S (torusParitySublattice d L) N := by
      rw [staggeredPhatS_eq_cartesian_sq, smul_smul,
        mul_inv_cancel₀ (pow_ne_zero 2 hVne), one_smul]
    have hI1 : staggeredOrderOp2S (torusParitySublattice d L) N
          * staggeredOrderOp2S (torusParitySublattice d L) N
        = ((L : ℂ) ^ d) ^ 2 • staggeredPhatS d L N
          - staggeredOrderOp1S (torusParitySublattice d L) N
            * staggeredOrderOp1S (torusParitySublattice d L) N := by
      rw [hV2]; abel
    have hI2 : staggeredOrderOp1S (torusParitySublattice d L) N
          * staggeredOrderOp1S (torusParitySublattice d L) N
        = (((L : ℂ) ^ d) ^ 2 / 4) • (Ã * Ã) := by
      rw [staggeredOrderOp1S_eq_smul_orderDensitySum, ← hÃ, smul_mul_smul_comm]
      congr 1
      ring
    -- move `Ã^k` onto `Φ` on both sides (Hermitian)
    have hh : Matrix.conjTranspose (Ã ^ k) = Ã ^ k := (hÃH.pow k).eq
    have hmove : ∀ M' : ManyBodyOpS (HypercubicTorus d L) N,
        star ((Ã ^ k).mulVec Φ) ⬝ᵥ M'.mulVec ((Ã ^ k).mulVec Φ)
          = star Φ ⬝ᵥ (Ã ^ k * M' * Ã ^ k).mulVec Φ := by
      intro M'
      calc star ((Ã ^ k).mulVec Φ) ⬝ᵥ M'.mulVec ((Ã ^ k).mulVec Φ)
          = star ((Matrix.conjTranspose (Ã ^ k)).mulVec Φ) ⬝ᵥ M'.mulVec ((Ã ^ k).mulVec Φ) := by
            rw [hh]
        _ = star Φ ⬝ᵥ (Ã ^ k).mulVec (M'.mulVec ((Ã ^ k).mulVec Φ)) :=
            (star_dotProduct_mulVec_conjTranspose (Ã ^ k) Φ _).symm
        _ = star Φ ⬝ᵥ (Ã ^ k * M' * Ã ^ k).mulVec Φ := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [hI1, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      hI2, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hmove, hmove,
      show Ã ^ k * (Ã * Ã) * Ã ^ k = Ã ^ (2 * (k + 1)) from by
        rw [← mul_assoc, ← pow_succ, ← pow_succ, ← pow_add]; congr 1; ring]
  have hden : star ((Ã ^ k).mulVec Φ) ⬝ᵥ (Ã ^ k).mulVec Φ
      = star Φ ⬝ᵥ (Ã ^ (2 * k)).mulVec Φ := by
    rw [hermitian_pow_dotProduct_split hÃH k k Φ, two_mul]
  have hnumre : (((L : ℂ) ^ d) ^ 2
        * (star Φ ⬝ᵥ (Ã ^ k * staggeredPhatS d L N * Ã ^ k).mulVec Φ)
      - ((L : ℂ) ^ d) ^ 2 / 4 * (star Φ ⬝ᵥ (Ã ^ (2 * (k + 1))).mulVec Φ)).re
      = ((L : ℝ) ^ d) ^ 2 * (star Φ ⬝ᵥ (Ã ^ k * staggeredPhatS d L N * Ã ^ k).mulVec Φ).re
        - ((L : ℝ) ^ d) ^ 2 / 4 * (star Φ ⬝ᵥ (Ã ^ (2 * (k + 1))).mulVec Φ).re := by
    rw [Complex.sub_re]
    congr 1
    · rw [Complex.mul_re, show ((L : ℂ) ^ d) ^ 2 = (((L : ℝ) ^ d) ^ 2 : ℝ) from by push_cast; ring,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    · rw [Complex.mul_re,
        show ((L : ℂ) ^ d) ^ 2 / 4 = (((L : ℝ) ^ d) ^ 2 / 4 : ℝ) from by push_cast; ring,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hmid, hden, hnumre, div_div]
  -- `(V²·E − (V²/4)·D')/(D_k·V²) = (4E − D')/(4 D_k)`; the volume factor cancels
  rcases eq_or_ne (star Φ ⬝ᵥ (Ã ^ (2 * k)).mulVec Φ).re 0 with h0 | hne
  · rw [h0]; simp
  · have hV2ne : ((L : ℝ) ^ d) ^ 2 ≠ 0 := by positivity
    rw [show (2 * (k + 1)) = 2 * k + 2 from by ring]
    field_simp

/-- **Abstract division bound** for the transverse fluctuation.  With `q = k+1`, central binomials
`c, c2` obeying the Pascal relation `q(4c − c2) = 2c`, and the F1/F2 pinches `num ≤ (2c/q)P' +
(4c+c2)β`, `4c(P − βk) ≤ den`, plus `P' ≤ N² P` and `βk ≤ P/2`, the ratio `num/den` is at most
`N²/(2q)` plus a clean `O(β + βk)` error. Pure real arithmetic. -/
private theorem delta_frac_bound (q c c2 P P' bet betk den n2 num : ℝ)
    (hq : 0 < q) (hc : 0 < c) (hP : 0 < P)
    (hbet : 0 ≤ bet) (hbetk : 0 ≤ betk) (hc2 : 0 ≤ c2) (hn2 : 0 ≤ n2) (hP' : 0 ≤ P')
    (hP'n2 : P' ≤ n2 * P) (hbetkhalf : betk ≤ P / 2)
    (hden : 4 * c * (P - betk) ≤ den)
    (hnum : num ≤ 2 * c / q * P' + (4 * c + c2) * bet) :
    num / den
      ≤ n2 / (2 * q) + ((4 * c + c2) * bet / (2 * c * P) + n2 * betk / (q * P)) := by
  have hW : 0 < P - betk := by linarith
  have h4cW : 0 < 4 * c * (P - betk) := by positivity
  have hdenpos : 0 < den := lt_of_lt_of_le h4cW hden
  -- `num/den ≤ A/(4c(P−βk))`
  have hA : 0 ≤ 2 * c / q * P' + (4 * c + c2) * bet := by positivity
  have hstep12 : num / den ≤ (2 * c / q * P' + (4 * c + c2) * bet) / (4 * c * (P - betk)) := by
    calc num / den ≤ (2 * c / q * P' + (4 * c + c2) * bet) / den := by gcongr
      _ ≤ (2 * c / q * P' + (4 * c + c2) * bet) / (4 * c * (P - betk)) :=
          div_le_div_of_nonneg_left hA h4cW hden
  refine le_trans hstep12 ?_
  -- split the upper numerator into the two fractions
  have hsplit : (2 * c / q * P' + (4 * c + c2) * bet) / (4 * c * (P - betk))
      = P' / (2 * q * (P - betk)) + (4 * c + c2) * bet / (4 * c * (P - betk)) := by
    rw [add_div]
    congr 1
    rw [div_mul_eq_mul_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [hsplit]
  -- `Term1 = P'/(2q(P−βk)) ≤ N²/(2q) + N²βk/(qP)`; the factor `q` cancels
  have hbase : P' / (P - betk) ≤ (n2 * P + 2 * n2 * betk) / P := by
    rw [div_le_div_iff₀ hW hP]
    nlinarith [mul_nonneg hP.le (by linarith [hP'n2] : (0 : ℝ) ≤ n2 * P - P'),
      mul_nonneg (mul_nonneg hn2 hbetk) (by linarith : (0 : ℝ) ≤ P - 2 * betk)]
  have hterm1 : P' / (2 * q * (P - betk)) ≤ n2 / (2 * q) + n2 * betk / (q * P) := by
    rw [show P' / (2 * q * (P - betk)) = P' / (P - betk) / (2 * q) from by
        rw [div_div, mul_comm (2 * q)],
      show n2 / (2 * q) + n2 * betk / (q * P) = (n2 * P + 2 * n2 * betk) / P / (2 * q) from by
        field_simp]
    gcongr
  -- `Term2 = (4c+c2)β/(4c(P−βk)) ≤ (4c+c2)β/(2cP)`
  have hterm2 : (4 * c + c2) * bet / (4 * c * (P - betk)) ≤ (4 * c + c2) * bet / (2 * c * P) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [hbetkhalf, hc.le]
  linarith [hterm1, hterm2]

/-- **Central-binomial Pascal identity (real form)**: `(k+1)(4 C(2k,k) − C(2k+2,k+1)) = 2 C(2k,k)`,
from `Nat.succ_mul_centralBinom_succ`.  This makes the leading coefficient `4c − c2 = 2c/(k+1)`. -/
private theorem pascal_real (k : ℕ) :
    ((k : ℝ) + 1) * (4 * ((2 * k).choose k : ℝ) - ((2 * (k + 1)).choose (k + 1) : ℝ))
      = 2 * ((2 * k).choose k : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have hr : ((k + 1) * (2 * (k + 1)).choose (k + 1) : ℝ)
      = (2 * (2 * k + 1) * (2 * k).choose k : ℝ) := by exact_mod_cast h
  push_cast at hr
  nlinarith [hr]

/-- The explicit finite-`L` upper bound on the transverse fluctuation `δ_{j+1}` (eq. (4.2.55)): the
sharp leading term `N²/(2(j+2))` from the central-binomial cancellation, plus a genuinely `O(1/V)`
error assembled from the F1/F2 fine bands. -/
noncomputable def deltaFluctBound (d L N j : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) : ℝ :=
  (N : ℝ) ^ 2 / (2 * ((j : ℝ) + 1 + 1))
    + ((4 * ((2 * (j + 1)).choose (j + 1) : ℝ) + ((2 * (j + 1 + 1)).choose (j + 1 + 1) : ℝ))
          * (((j : ℝ) + 1 + 1) ^ 2
            * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ (j + 1))))
          / (2 * ((2 * (j + 1)).choose (j + 1) : ℝ) * phatMoment d L N Φ (j + 1))
      + (N : ℝ) ^ 2
          * (((j : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ j)))
          / (((j : ℝ) + 1 + 1) * phatMoment d L N Φ (j + 1)))

set_option maxHeartbeats 3200000 in
-- The final assembly elaborates several large order-word expectation terms against the abstract
-- division bound, exceeding the default heartbeat budget.
/-- **[F3] Transverse fluctuation decay bound (eq. (4.2.55)).**  Under long-range order (`0 < q₀`)
and the size condition `3 N (j+2)² ≤ 2 q₀ V`, the per-site transverse fluctuation of the tower term
`u_{j+1}` obeys `δ_{j+1} ≤ N²/(2(j+2)) + O(1/V)` (`deltaFluctBound`).  The sharp leading term of the
central-binomial Pascal cancellation (`pascal_real`), the fine two-sided pinches of the denominator
(`orderSum_pow_two_denom_close`) and the `p̂`-insertion (`orderSum_pow_phat_insert_close`), and the
Rayleigh power ratio (`phatMoment_succ_le_normSq`); the volume factors cancel via `tanaka_delta_eq`.
The error term is `O(1/V)` (each fine band carries an explicit `N/V`). -/
theorem tanaka_delta_le (d L N j : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1)
    (hcond : 3 * (N : ℝ) * ((j : ℝ) + 1 + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    (star (tanakaTowerTerm (torusParitySublattice d L) N (j + 1) Φ)
        ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
          * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec
          (tanakaTowerTerm (torusParitySublattice d L) N (j + 1) Φ)).re
        / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (j + 1) Φ) / ((L : ℝ) ^ d) ^ 2
      ≤ deltaFluctBound d L N j Φ := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  -- size conditions (native cast form at `j+1`, plain at `j`)
  have hcond1 : 3 * (N : ℝ) * (((j + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d := by
    push_cast; nlinarith [hcond]
  have hcondj : 3 * (N : ℝ) * ((j : ℝ) + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d := by
    have hle : ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1 + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
    nlinarith [hcond, mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 3 * (N : ℝ))]
  -- positivity
  have hcpos : (0 : ℝ) < ((2 * (j + 1)).choose (j + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hPcpos : 0 < phatMoment d L N Φ (j + 1) := by
    have hge := phatMoment_ge_of_lro d L N Φ hq₀.le hm0 hlro j
    have hpos : 0 < (2 * q₀) ^ (j + 1) * phatMoment d L N Φ 0 :=
      mul_pos (pow_pos (by linarith) (j + 1)) hm0
    exact lt_of_lt_of_le hpos hge
  have hPjnn : 0 ≤ phatMoment d L N Φ j := phatMoment_nonneg d L N Φ j
  -- F2 at `j+1`, F1 at `j+1`, F1 at `j`; normalize casts to `↑j + 1`
  have hcast : ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 1 + 1 := by push_cast; ring
  have hF2 := orderSum_pow_phat_insert_close d L N hN Φ hsing3 hm0 hlro (j + 1) hcond1
  rw [abs_le, hcast] at hF2
  have hF1' := orderSum_pow_two_denom_close d L N hN Φ hsing3 hm0 hlro (j + 1) hcond1
  rw [abs_le, hcast] at hF1'
  have hF1 := orderSum_pow_two_denom_close d L N hN Φ hsing3 hm0 hlro j hcondj
  rw [abs_le] at hF1
  -- Gap2 and the `betk ≤ Pc/2` collapse
  have hP'n2 := phatMoment_succ_le_normSq d L N hN Φ (j + 1)
  have hNV : (N : ℝ) / (L : ℝ) ^ d * ((j : ℝ) + 1) ^ 2 ≤ 2 * q₀ / 3 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hVpos]; nlinarith [hcondj]
  have hratio := phatMoment_succ_ratio d L N Φ hm0 hlro j
  have hbetkhalf : ((j : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ j))
      ≤ phatMoment d L N Φ (j + 1) / 2 := by
    have h1 : ((j : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ j))
        ≤ q₀ * phatMoment d L N Φ j := by
      have hmul := mul_le_mul_of_nonneg_right hNV
        (by positivity : (0 : ℝ) ≤ 3 / 2 * phatMoment d L N Φ j)
      nlinarith [hmul, hPjnn]
    nlinarith [h1, hratio, hq₀, hPjnn]
  -- Pascal `4c - c2 = 2c/q`
  have hpasc := pascal_real (j + 1)
  have h4c_c2 : 4 * ((2 * (j + 1)).choose (j + 1) : ℝ) - ((2 * (j + 1 + 1)).choose (j + 1 + 1) : ℝ)
      = 2 * ((2 * (j + 1)).choose (j + 1) : ℝ) / ((j : ℝ) + 1 + 1) := by
    rw [eq_div_iff (by positivity)]
    have : (((j + 1 : ℕ) : ℝ) + 1) = (j : ℝ) + 1 + 1 := by push_cast; ring
    rw [this] at hpasc; linarith [hpasc]
  -- convert the goal to the `D/E` ratio, then abstract the three large expectations as reals
  rw [tanaka_delta_eq d L N (j + 1) Φ]
  set E := (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
      + staggeredOrderDensityOpS d L N false) ^ (j + 1) * staggeredPhatS d L N
      * (staggeredOrderDensityOpS d L N true
        + staggeredOrderDensityOpS d L N false) ^ (j + 1)).mulVec Φ).re with hEdef
  set Dnext := (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
      + staggeredOrderDensityOpS d L N false) ^ (2 * (j + 1 + 1))).mulVec Φ).re with hDnextdef
  set Dcur := (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
      + staggeredOrderDensityOpS d L N false) ^ (2 * (j + 1))).mulVec Φ).re with hDcurdef
  -- numerator/denominator bounds (small terms now)
  have hnum : 4 * E - Dnext
      ≤ 2 * ((2 * (j + 1)).choose (j + 1) : ℝ) / ((j : ℝ) + 1 + 1) * phatMoment d L N Φ (j + 1 + 1)
        + (4 * ((2 * (j + 1)).choose (j + 1) : ℝ) + ((2 * (j + 1 + 1)).choose (j + 1 + 1) : ℝ))
          * (((j : ℝ) + 1 + 1) ^ 2
            * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ (j + 1)))) := by
    rw [← h4c_c2]; nlinarith [hF2.2, hF1'.1]
  have hden : 4 * ((2 * (j + 1)).choose (j + 1) : ℝ)
        * (phatMoment d L N Φ (j + 1)
          - ((j : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ j)))
      ≤ 4 * Dcur := by
    nlinarith [hF1.1]
  rw [deltaFluctBound]
  exact delta_frac_bound ((j : ℝ) + 1 + 1) ((2 * (j + 1)).choose (j + 1) : ℝ)
    ((2 * (j + 1 + 1)).choose (j + 1 + 1) : ℝ) (phatMoment d L N Φ (j + 1))
    (phatMoment d L N Φ (j + 1 + 1))
    (((j : ℝ) + 1 + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ (j + 1))))
    (((j : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ j)))
    (4 * Dcur) ((N : ℝ) ^ 2) (4 * E - Dnext)
    (by positivity) hcpos hPcpos
    (by have := phatMoment_nonneg d L N Φ (j + 1); positivity)
    (by have := phatMoment_nonneg d L N Φ j; positivity) (by positivity) (by positivity)
    (phatMoment_nonneg d L N Φ (j + 1 + 1)) hP'n2 hbetkhalf hden hnum

/-- **[F4/F3] Axis-2 fluctuation decay, finite-`L` form (eq. (4.2.15)).**  The Tanaka state's axis-2
squared per-site moment is the average of the two transverse fluctuations, each bounded by
`tanaka_delta_le`: `second2 ≤ ½(deltaFluctBound i + deltaFluctBound (i+1))`, where `M = i+1`.  Both
summands have the sharp leading term `N²/(2·)` from the central-binomial cancellation plus an
`O(1/V)` remainder, so the bound `→ 0` as `M → ∞` with `M²/V → 0` (the `ε`-convergence is assembled
in the capstone PR).  Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §4.2.2, eq. (4.2.15)/(4.2.49)–(4.2.55), pp. 106–108. -/
theorem tanakaOrderSecond2_le (d L N i : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1)
    (hcond : 3 * (N : ℝ) * ((i : ℝ) + 1 + 1 + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hBM : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (i + 1) Φ))
    (hBM1 : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (i + 1 + 1) Φ)) :
    tanakaOrderSecond2 d L N (i + 1) Φ
      ≤ 1 / 2 * (deltaFluctBound d L N i Φ + deltaFluctBound d L N (i + 1) Φ) := by
  have hcondi : 3 * (N : ℝ) * ((i : ℝ) + 1 + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d := by
    have hle : ((i : ℝ) + 1 + 1) ^ 2 ≤ ((i : ℝ) + 1 + 1 + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) i]
    nlinarith [hcond, mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 3 * (N : ℝ))]
  have hcondi1 : 3 * (N : ℝ) * (((i + 1 : ℕ) : ℝ) + 1 + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d := by
    have hcast : (((i + 1 : ℕ) : ℝ) + 1 + 1) = (i : ℝ) + 1 + 1 + 1 := by push_cast; ring
    rw [hcast]; exact hcond
  have hd1 := tanaka_delta_le d L N i hN Φ hsing3 hq₀ hm0 hlro hcondi
  have hd2 := tanaka_delta_le d L N (i + 1) hN Φ hsing3 hq₀ hm0 hlro hcondi1
  rw [tanakaOrderSecond2_eq_half_sum d L N (i + 1) Φ hsing3 hBM hBM1, mul_div_assoc, add_div,
    mul_add]
  linarith [hd1, hd2]

end LatticeSystem.Quantum
