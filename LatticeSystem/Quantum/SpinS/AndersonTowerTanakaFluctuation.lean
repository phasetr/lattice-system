/-
Tasaki §4.2.2 Theorem 4.9 (the Tanaka state exhibits full symmetry breaking), arc PR4 — the axis-2
transverse fluctuation decay (4.2.15), `lim_{L↑∞} ⟨Ξ| (Ô_L^{(2)}/L^d)² |Ξ⟩ = 0`.

The mechanism (Tasaki eqs. (4.2.49)–(4.2.55), pp. 106–108).  Write `Ã := ô⁺ + ô⁻` (so
`Ô_L^{(1)} = (V/2) Ã`, `V = L^d`) and `P_k := ⟨Φ, p̂^k Φ⟩` (`phatMoment`).  The per-site transverse
fluctuation of the tower term `u_k` is
`δ_k := ⟨u_k| (ô^{(2)})² |u_k⟩ = ⟨tt_k, (Ô^{(2)})² tt_k⟩ / (B_k V²)` with `B_k = ‖(Ô_L^{(1)})^k Φ‖²`.
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

end LatticeSystem.Quantum
