import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundSectorWords

/-!
# Tasaki §4.2.1 Theorem 4.6: swap-chain telescoping, the R1 induction, and tower corollaries

The swap-chain telescoping estimate and the resulting R1 induction bounding balanced order-word
products (P8-5), and its corollaries: the tower denominator lower bound
`tower_denominator_lower_bound` and the well-definedness identities used downstream (P8-6).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1–§4.2.2, Theorem 4.6, eqs. (4.2.3)–(4.2.7), (4.2.35); cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Swap-chain telescoping and the R1 induction (P8-5) -/

/-- An adjacent transposition preserves each letter count. -/
theorem AdjSwap.count_eq {w w' : List Bool} (h : AdjSwap w w') (c : Bool) :
    w.count c = w'.count c := by
  obtain ⟨pre, suf, a, b, rfl, rfl⟩ := h
  simp only [List.count_append, List.count_cons]
  ring

/-- **Per-swap real-expectation bound for balanced words**: for a balanced length-`2n` word `w`, one
adjacent transposition changes `Re b_w` by at most `(N/V)·B`, where `B` bounds the real expectations
of balanced length-`2(n−1)` words. -/
theorem adjSwap_re_diff_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbnd : ∀ u : List Bool, u.count true = n - 1 → u.count false = n - 1 →
        |(star Φ ⬝ᵥ (orderWordProd d L N u).mulVec Φ).re| ≤ B)
    {w w' : List Bool} (h : AdjSwap w w') (hwt : w.count true = n) (hwf : w.count false = n) :
    |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re
        - (star Φ ⬝ᵥ (orderWordProd d L N w').mulVec Φ).re|
      ≤ (N : ℝ) / (L : ℝ) ^ d * B := by
  obtain ⟨pre, suf, a, b, rfl, rfl⟩ := h
  rcases a with _ | _ <;> rcases b with _ | _
  · -- (false, false): w = w'
    simp only [sub_self, abs_zero]; positivity
  · -- (false, true)
    refine le_trans (orderWordProd_swap_re_diff_le d L N hN Φ hsing pre suf false true) ?_
    refine mul_le_mul_of_nonneg_left (hbnd _ ?_ ?_) (by positivity)
    · simp at hwt ⊢; omega
    · simp at hwf ⊢; omega
  · -- (true, false)
    refine le_trans (orderWordProd_swap_re_diff_le d L N hN Φ hsing pre suf true false) ?_
    refine mul_le_mul_of_nonneg_left (hbnd _ ?_ ?_) (by positivity)
    · simp at hwt ⊢; omega
    · simp at hwf ⊢; omega
  · -- (true, true): w = w'
    simp only [sub_self, abs_zero]; positivity

/-- **Swap-chain telescoping**: a length-`k` swap chain between balanced length-`2n` words changes
`Re b` by at most `k·(N/V)·B`. -/
theorem swapChain_re_diff_le (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) (n : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbnd : ∀ u : List Bool, u.count true = n - 1 → u.count false = n - 1 →
        |(star Φ ⬝ᵥ (orderWordProd d L N u).mulVec Φ).re| ≤ B)
    {k : ℕ} {w w' : List Bool} (hc : SwapChain k w w') :
    w.count true = n → w.count false = n →
    |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re
        - (star Φ ⬝ᵥ (orderWordProd d L N w').mulVec Φ).re|
      ≤ (k : ℝ) * ((N : ℝ) / (L : ℝ) ^ d * B) := by
  induction hc with
  | refl w => intro _ _; simp
  | @step j w w' w'' hs hchain ih =>
    intro hwt hwf
    have hw't : w'.count true = n := by rw [← hs.count_eq true]; exact hwt
    have hw'f : w'.count false = n := by rw [← hs.count_eq false]; exact hwf
    have h1 := adjSwap_re_diff_le d L N hN Φ hsing n B hB hbnd hs hwt hwf
    have ih' := ih hw't hw'f
    calc |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re
            - (star Φ ⬝ᵥ (orderWordProd d L N w'').mulVec Φ).re|
        ≤ |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re
              - (star Φ ⬝ᵥ (orderWordProd d L N w').mulVec Φ).re|
          + |(star Φ ⬝ᵥ (orderWordProd d L N w').mulVec Φ).re
              - (star Φ ⬝ᵥ (orderWordProd d L N w'').mulVec Φ).re| := abs_sub_le _ _ _
      _ ≤ (N : ℝ) / (L : ℝ) ^ d * B + (j : ℝ) * ((N : ℝ) / (L : ℝ) ^ d * B) :=
          add_le_add h1 ih'
      _ = ((j : ℝ) + 1) * ((N : ℝ) / (L : ℝ) ^ d * B) := by ring
      _ = ((j + 1 : ℕ) : ℝ) * ((N : ℝ) / (L : ℝ) ^ d * B) := by push_cast; ring

/-- `P_n` is the uniform `(½)ⁿ`-average of the real block-word expectations. -/
theorem phatMoment_eq_blockWord_avg (d L N n : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) :
    phatMoment d L N Φ n
      = (2⁻¹ : ℝ) ^ n
          * ∑ c : Fin n → Bool,
              (star Φ ⬝ᵥ (orderWordProd d L N (blockWord c)).mulVec Φ).re := by
  rw [phatMoment, staggeredPhatS_pow_eq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Matrix.sum_mulVec, dotProduct_sum,
    show ((2 : ℂ)⁻¹) ^ n = (((2⁻¹ : ℝ) ^ n : ℝ) : ℂ) from by push_cast; ring,
    Complex.re_ofReal_mul, Complex.re_sum]

set_option maxHeartbeats 800000 in
-- The nested swap-chain + block-word-average kernel exceeds the default heartbeat budget.
/-- **Non-recursive swap-chain + block-word-average kernel (eq. (4.2.34)).**  Given a uniform
bound `B` on the real expectations of balanced length-`2m` order words, every balanced length-
`2(m+1)` word `w` has real expectation within `(m+1)² (N/V) B` of `P_{m+1}`.  The proof combines
the renormalized swap-chain estimate (`swapChain_re_diff_le`) with the block-word average
(`abs_sub_smul_sum_le`).  This kernel carries the weakest possible hypotheses (no `q₀`, no
low-energy condition): both the crude `½ P`-collapse (`orderWord_balanced_re_close`) and the fine
`O(1/V)` two-sided bound (`orderWord_balanced_re_close_fine`) invoke it, so the swap-chain
machinery is written exactly once. -/
private theorem orderWord_balanced_re_close_step (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) (m : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbnd : ∀ u : List Bool, u.count true = m → u.count false = m →
        |(star Φ ⬝ᵥ (orderWordProd d L N u).mulVec Φ).re| ≤ B)
    (w : List Bool) (hwt : w.count true = m + 1) (hwf : w.count false = m + 1) :
    |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re - phatMoment d L N Φ (m + 1)|
      ≤ ((m : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * B) := by
  -- per-block-word deviation bound
  have hbnd' : ∀ u : List Bool, u.count true = m + 1 - 1 → u.count false = m + 1 - 1 →
      |(star Φ ⬝ᵥ (orderWordProd d L N u).mulVec Φ).re| ≤ B := by
    intro u hut huf
    rw [Nat.add_sub_cancel] at hut huf
    exact hbnd u hut huf
  have hper : ∀ c : Fin (m + 1) → Bool,
      |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re
          - (star Φ ⬝ᵥ (orderWordProd d L N (blockWord c)).mulVec Φ).re|
        ≤ ((m : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * B) := by
    intro c
    have hperm : w.Perm (blockWord c) :=
      binary_perm_of_count
        (by rw [blockWord_length]; have := count_true_add_count_false w; omega)
        (by rw [blockWord_count_true]; exact hwt)
    obtain ⟨k, hk, hchain⟩ := swapDist_le hperm
    have hchainbd := swapChain_re_diff_le d L N hN Φ hsing (m + 1) B hB hbnd' hchain hwt hwf
    refine le_trans hchainbd ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hkle : (k : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
      have hk2 : k ≤ (m + 1) * (m + 1) := by rw [hwt, hwf] at hk; exact hk
      calc (k : ℝ) ≤ ((m + 1) * (m + 1) : ℕ) := by exact_mod_cast hk2
        _ = ((m : ℝ) + 1) ^ 2 := by push_cast; ring
    exact hkle
  -- deviation of w from the block-word average ≤ D
  rw [phatMoment_eq_blockWord_avg]
  refine abs_sub_smul_sum_le Finset.univ ((2⁻¹ : ℝ) ^ (m + 1)) (by positivity) _ _ _ ?_ ?_
  · rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    push_cast
    rw [← mul_pow, show (2⁻¹ : ℝ) * 2 = 1 from by norm_num, one_pow]
  · intro c _; exact hper c

set_option maxHeartbeats 800000 in
-- The `n`-induction chaining the shared kernel with the moment-ratio collapse is heartbeat-heavy.
/-- **Lemma R1, deviation form (eq. (4.2.67)).**  Under `3 N n² ≤ 2 q₀ V`, every balanced
length-`2n` order word has real expectation within `½ P_n` of `P_n`.  Proved by induction on `n`:
the renormalized swap-chain estimate (`swapChain_re_diff_le`) bounds the deviation of each word from
the block-word average by `n² (N/V) (3/2) P_{n-1}`, and `P_{n-1} ≤ P_n/(2q₀)` collapses this to
`½ P_n`. -/
theorem orderWord_balanced_re_close (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1) :
    ∀ (n : ℕ), 3 * (N : ℝ) * (n : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d →
      ∀ w : List Bool, w.count true = n → w.count false = n →
        |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re - phatMoment d L N Φ n|
          ≤ (1 / 2) * phatMoment d L N Φ n := by
  intro n
  induction n with
  | zero =>
    intro _ w hwt hwf
    have hwnil : w = [] := by
      have hlen : w.length = 0 := by
        have := count_true_add_count_false w; omega
      exact List.length_eq_zero_iff.mp hlen
    subst hwnil
    have hb : (star Φ ⬝ᵥ (orderWordProd d L N []).mulVec Φ).re = phatMoment d L N Φ 0 := by
      rw [phatMoment_zero]
      simp only [orderWordProd, List.map_nil, List.prod_nil, Matrix.one_mulVec]
    rw [hb, sub_self, abs_zero]
    have := phatMoment_nonneg d L N Φ 0
    positivity
  | succ m ih =>
    intro hcond w hwt hwf
    have hLpos : (0 : ℝ) < (L : ℝ) ^ d := by
      have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    have hPm : 0 ≤ phatMoment d L N Φ m := phatMoment_nonneg d L N Φ m
    have hPm1 : 0 ≤ phatMoment d L N Φ (m + 1) := phatMoment_nonneg d L N Φ (m + 1)
    -- inductive hypothesis at m
    have hcondm : 3 * (N : ℝ) * (m : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d := by
      refine le_trans ?_ hcond
      have : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) N, this]
    have ihm := ih hcondm
    -- uniform bound B = (3/2) P_m on balanced length-2m words
    have hbnd : ∀ u : List Bool, u.count true = m → u.count false = m →
        |(star Φ ⬝ᵥ (orderWordProd d L N u).mulVec Φ).re| ≤ 3 / 2 * phatMoment d L N Φ m := by
      intro u hut huf
      have hd := ihm u hut huf
      have h2 := abs_sub_le (star Φ ⬝ᵥ (orderWordProd d L N u).mulVec Φ).re
        (phatMoment d L N Φ m) 0
      rw [sub_zero, sub_zero, abs_of_nonneg hPm] at h2
      linarith [hd, h2]
    -- deviation of w from the block-word average ≤ D, via the shared swap-chain kernel
    have hdev := orderWord_balanced_re_close_step d L N hN Φ hsing m
      (3 / 2 * phatMoment d L N Φ m) (by positivity) hbnd w hwt hwf
    -- D ≤ ½ P_{m+1} via the moment ratio
    refine le_trans hdev ?_
    have hratio : 2 * q₀ * phatMoment d L N Φ m ≤ phatMoment d L N Φ (m + 1) :=
      phatMoment_succ_ratio d L N Φ hm0 hlro m
    have hNV : (N : ℝ) / (L : ℝ) ^ d * ((m : ℝ) + 1) ^ 2 ≤ 2 * q₀ / 3 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hLpos]
      push_cast at hcond
      nlinarith [hcond, hLpos]
    calc ((m : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ m))
        = 3 / 2 * phatMoment d L N Φ m * ((N : ℝ) / (L : ℝ) ^ d * ((m : ℝ) + 1) ^ 2) := by ring
      _ ≤ 3 / 2 * phatMoment d L N Φ m * (2 * q₀ / 3) :=
          mul_le_mul_of_nonneg_left hNV (by positivity)
      _ = q₀ * phatMoment d L N Φ m := by ring
      _ ≤ 1 / 2 * phatMoment d L N Φ (m + 1) := by linarith [hratio]

set_option maxHeartbeats 800000 in
-- Elaborating the shared-kernel application against the `phatMoment` band is heartbeat-heavy.
/-- **Lemma R1, fine two-sided form (eq. (4.2.34)).**  Under `3 N (m+1)² ≤ 2 q₀ V`, every balanced
length-`2(m+1)` order word has real expectation within the genuinely `O(1/V)` band
`(m+1)² (N/V) (3/2 P_m)` of `P_{m+1}`.  Unlike the crude `½ P_{m+1}` collapse
(`orderWord_balanced_re_close`), the `(m+1)² N/V` prefactor is retained; this is what resolves the
central-binomial Pascal cancellation in the axis-2 fluctuation decay (4.2.15).  Proved by feeding
the crude closeness at `m` into the shared swap-chain kernel `orderWord_balanced_re_close_step`. -/
theorem orderWord_balanced_re_close_fine (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1) (m : ℕ)
    (hcond : 3 * (N : ℝ) * ((m : ℝ) + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (w : List Bool) (hwt : w.count true = m + 1) (hwf : w.count false = m + 1) :
    |(star Φ ⬝ᵥ (orderWordProd d L N w).mulVec Φ).re - phatMoment d L N Φ (m + 1)|
      ≤ ((m : ℝ) + 1) ^ 2 * ((N : ℝ) / (L : ℝ) ^ d * (3 / 2 * phatMoment d L N Φ m)) := by
  have hPm : 0 ≤ phatMoment d L N Φ m := phatMoment_nonneg d L N Φ m
  -- crude closeness at `m` (its hypothesis follows from `hcond` since `m² ≤ (m+1)²`)
  have hcondm : 3 * (N : ℝ) * (m : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d := by
    refine le_trans ?_ hcond
    have : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
    nlinarith [Nat.cast_nonneg (α := ℝ) N, this]
  have hcrude := orderWord_balanced_re_close d L N hN Φ hsing hm0 hlro m hcondm
  -- convert crude closeness (`|· − P_m| ≤ ½ P_m`) into a uniform absolute bound `3/2 P_m`
  have hbnd : ∀ u : List Bool, u.count true = m → u.count false = m →
      |(star Φ ⬝ᵥ (orderWordProd d L N u).mulVec Φ).re| ≤ 3 / 2 * phatMoment d L N Φ m := by
    intro u hut huf
    have hd := hcrude u hut huf
    have h2 := abs_sub_le (star Φ ⬝ᵥ (orderWordProd d L N u).mulVec Φ).re
      (phatMoment d L N Φ m) 0
    rw [sub_zero, sub_zero, abs_of_nonneg hPm] at h2
    linarith [hd, h2]
  exact orderWord_balanced_re_close_step d L N hN Φ hsing m
    (3 / 2 * phatMoment d L N Φ m) (by positivity) hbnd w hwt hwf

/-! ### R1 corollaries: tower denominator lower bound and well-definedness (P8-6) -/

/-- **Tower denominator lower bound** (eq. (4.2.67) applied to `(ô⁻)^M (ô⁺)^M`): under
`3 N M² ≤ 2 q₀ V`, the squared per-volume tower amplitude obeys `½ P_M ≤ ⟨Φ, (ô⁻)^M (ô⁺)^M Φ⟩`. -/
theorem tower_denominator_lower_bound (d L N : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ}
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1)
    {M : ℕ} (hcond : 3 * (N : ℝ) * (M : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    (1 / 2) * phatMoment d L N Φ M
      ≤ (star Φ ⬝ᵥ (staggeredOrderDensityOpS d L N false ^ M
          * staggeredOrderDensityOpS d L N true ^ M).mulVec Φ).re := by
  have hwt : (List.replicate M false ++ List.replicate M true).count true = M := by
    simp [List.count_append, List.count_replicate]
  have hwf : (List.replicate M false ++ List.replicate M true).count false = M := by
    simp [List.count_append, List.count_replicate]
  have heq : orderWordProd d L N (List.replicate M false ++ List.replicate M true)
      = staggeredOrderDensityOpS d L N false ^ M * staggeredOrderDensityOpS d L N true ^ M := by
    rw [orderWordProd, List.map_append, List.map_replicate, List.map_replicate, List.prod_append,
      List.prod_replicate, List.prod_replicate]
  have hclose := orderWord_balanced_re_close d L N hN Φ hsing hm0 hlro M hcond
    (List.replicate M false ++ List.replicate M true) hwt hwf
  rw [abs_le] at hclose
  rw [← heq]
  linarith [hclose.1]

/-- The staggered raising operator is `V` times the per-volume density: `Ô⁺ = V ô⁺`. -/
theorem staggeredRaisingOpS_eq_smul (d L N : ℕ) [NeZero L] :
    staggeredRaisingOpS (torusParitySublattice d L) N
      = ((L : ℂ) ^ d) • staggeredOrderDensityOpS d L N true := by
  rw [show staggeredOrderDensityOpS d L N true
      = ((L : ℂ) ^ d)⁻¹ • staggeredRaisingOpS (torusParitySublattice d L) N from rfl, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne L))), one_smul]

/-- `(ô⁻)^M` is the conjugate transpose of `(ô⁺)^M`. -/
theorem orderDensityFalse_pow_eq_conjTranspose (d L N M : ℕ) [NeZero L] :
    staggeredOrderDensityOpS d L N false ^ M
      = Matrix.conjTranspose (staggeredOrderDensityOpS d L N true ^ M) := by
  rw [staggeredOrderDensityOpS_false_eq_conjTranspose, Matrix.conjTranspose_pow]

end LatticeSystem.Quantum
