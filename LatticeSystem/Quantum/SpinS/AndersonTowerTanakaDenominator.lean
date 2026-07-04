/-
Tasaki §4.2.2 Theorem 4.8 (Tanaka symmetry-breaking state), crux sub-arc PR-B — the denominator
lower bound.

The Rayleigh quotient controlling the Tanaka tower term `(Ô_L^{(1)})^k Φ` has, after the
scale-invariance drop (`tanakaTowerTerm_expectationRatioRe_eq`), denominator
`D̃ = ⟨Φ, Ã^{2M} Φ⟩` with `Ã = ô⁺ + ô⁻`.  Expanding `Ã^{2M}` into the `2^{2M}` order words
(`orderDensitySum_pow_eq_sum_words`) and testing against the `Ŝ_tot^{(3)}`-singlet `Φ`
(eq. (4.1.7)), the charge-selection rule kills every *unbalanced* word (net charge `m(w) ≠ 0`), so
only the `C(2M, M)` *balanced* words survive; each balanced word contributes at least `½ P_M` by the
renormalized-product estimate `orderWord_balanced_re_close` (Lemma R1, eq. (4.2.67)).  This yields
the denominator lower bound `D̃ ≥ C(2M, M) · ½ P_M`, the `C(2M, M)` factor being one half of the
central binomial cancellation `C(2M-2, M-1)/C(2M, M) = M/(2(2M-1))` that drives the crux.

This file provides only the denominator lower bound consumed by the later crux PRs (PR-C
telescoping/charge decomposition, PR-D numerator assembly, PR-E capstone).  It touches none of the
numerator core.  All order-word leaf bounds are word-generic and reused verbatim.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, §4.2.2, pp. 111–112,
eqs. (4.1.7), (4.2.10), (4.2.67), (4.2.70), (4.2.71); Tanaka [62]/[66].
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSumExpansion

namespace LatticeSystem.Quantum

open Matrix

/-! ### Net charge in terms of the letter counts -/

/-- The net magnetization charge equals the signed letter-count difference,
`m(w) = #{true} − #{false}` (as a complex number).  Proved by induction, peeling one letter and
using `mCharge_cons` together with the `List.count` recursion. -/
theorem mCharge_eq_count (w : List Bool) :
    mCharge w = (w.count true : ℂ) - (w.count false : ℂ) := by
  induction w with
  | nil => simp
  | cons b t ih =>
    rw [mCharge_cons, ih]
    cases b <;> · simp only [List.count_cons]; norm_num; ring

/-! ### Balanced-word count = central binomial coefficient -/

/-- **Balanced-word counting** (word-sum multiplicity): the number of binary words `List.ofFn c`
(`c : Fin n → Bool`) with exactly `M` `true`-letters is the binomial coefficient `C(n, M)`.  Proved
by the bijection `c ↦ {k | c k = true}` between such words and the `M`-element subsets of `Fin n`,
whose count is `card_powersetCard`. -/
theorem card_ofFn_count_true_eq (n M : ℕ) :
    (Finset.univ.filter
        (fun c : Fin n → Bool => (List.ofFn c).count true = M)).card = n.choose M := by
  have hcard : (Finset.univ.filter
      (fun c : Fin n → Bool => (List.ofFn c).count true = M)).card
      = ((Finset.univ : Finset (Fin n)).powersetCard M).card := by
    refine Finset.card_nbij'
      (fun c => Finset.univ.filter (fun k => c k = true))
      (fun s => fun k => decide (k ∈ s)) ?_ ?_ ?_ ?_
    · intro c hc
      rw [Finset.mem_coe, Finset.mem_filter] at hc
      rw [Finset.mem_coe, Finset.mem_powersetCard_univ, ← count_true_ofFn]
      exact hc.2
    · intro s hs
      rw [Finset.mem_coe, Finset.mem_powersetCard_univ] at hs
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [count_true_ofFn]
      have hfilter : (Finset.univ.filter (fun i => decide (i ∈ s) = true))
          = Finset.univ.filter (fun i => i ∈ s) := by
        apply Finset.filter_congr
        intro i _; simp
      rw [hfilter, Finset.filter_univ_mem]
      exact hs
    · intro c _
      funext k
      by_cases h : c k = true
      · have hmem : k ∈ Finset.univ.filter (fun k => c k = true) := by
          rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
        change decide (k ∈ Finset.univ.filter (fun k => c k = true)) = c k
        rw [h]; exact decide_eq_true_eq.mpr hmem
      · have hnmem : k ∉ Finset.univ.filter (fun k => c k = true) := by
          intro hmem; rw [Finset.mem_filter] at hmem; exact h hmem.2
        change decide (k ∈ Finset.univ.filter (fun k => c k = true)) = c k
        rw [Bool.eq_false_iff.mpr h]; exact decide_eq_false_iff_not.mpr hnmem
    · intro s _
      ext k
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, decide_eq_true_eq]
  rw [hcard, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-! ### Denominator lower bound (eqs. (4.2.67)/(4.2.71) density side) -/

/-- **Tanaka denominator lower bound** ([N3], eqs. (4.2.67)/(4.2.71)): on a `Ŝ_tot^{(3)}`-singlet
`Φ` (eq. (4.1.7)), under the size condition `3 N M² ≤ 2 q₀ V`, the summed-density denominator obeys
`⟨Φ, (ô⁺ + ô⁻)^{2M} Φ⟩ ≥ C(2M, M) · ½ P_M`.

Proof: expand `Ã^{2M}` into the `2^{2M}` order words; the singlet charge-selection rule
(`dotProduct_orderWord_singlet_eq_zero_of_charge_ne`) kills every unbalanced word
(`#{true} ≠ M ⟹ m(w) ≠ 0`), leaving the `C(2M, M)` balanced words
(`card_ofFn_count_true_eq`), each `≥ ½ P_M` by `orderWord_balanced_re_close` (Lemma R1). -/
theorem orderSum_pow_two_denom_lower (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1)
    {M : ℕ} (hcond : 3 * (N : ℝ) * (M : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    ((2 * M).choose M : ℝ) * ((1 / 2) * phatMoment d L N Φ M)
      ≤ (star Φ ⬝ᵥ ((staggeredOrderDensityOpS d L N true
          + staggeredOrderDensityOpS d L N false) ^ (2 * M)).mulVec Φ).re := by
  rw [orderDensitySum_pow_eq_sum_words, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun c : Fin (2 * M) → Bool => (List.ofFn c).count true = M)]
  -- the unbalanced words carry a nonzero charge, so their expectations vanish
  have hunbal : ∑ c ∈ Finset.univ.filter
        (fun c : Fin (2 * M) → Bool => ¬ (List.ofFn c).count true = M),
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
  -- each balanced word contributes at least ½ P_M, and there are C(2M, M) of them
  have hbal : ((2 * M).choose M : ℝ) * ((1 / 2) * phatMoment d L N Φ M)
      = (Finset.univ.filter
          (fun c : Fin (2 * M) → Bool => (List.ofFn c).count true = M)).card
        • ((1 / 2) * phatMoment d L N Φ M) := by
    rw [card_ofFn_count_true_eq, nsmul_eq_mul]
  rw [hbal]
  refine Finset.card_nsmul_le_sum _ _ _ (fun c hc => ?_)
  rw [Finset.mem_filter] at hc
  have hwt := hc.2
  have hwf : (List.ofFn c).count false = M := by
    have hlen := count_true_add_count_false (List.ofFn c)
    rw [List.length_ofFn, hwt] at hlen
    omega
  have hclose := orderWord_balanced_re_close d L N hN Φ hsing hm0 hlro M hcond
    (List.ofFn c) hwt hwf
  rw [abs_le] at hclose
  linarith [hclose.1]

end LatticeSystem.Quantum
