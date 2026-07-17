import LatticeSystem.Quantum.SpinS.LiebSchultzMattisGlobalLocalReduction

/-!
# Tasaki §6.2 Lemma 6.4 (PR-5): the centered local twist generator norm bound `‖M̂_x‖ ≤ B/L`

The generalized Lieb–Schultz–Mattis discharge (Lemma 6.4) reduces the conjugation of each local
term `ĥ_x` to a conjugation by the centered local twist generator
`M̂_x = localTwistGen L N r x = Σ_{y∈W_x} (2π/L)·δ(x,y)·Ŝ_y^{(3)}` (Tasaki eq. (6.2.27)).  The
second-order symmetric-difference bound of the twist conjugation (PR-6/PR-7) is `O(‖M̂_x‖²)`, so a
uniform `‖M̂_x‖ ≤ B/L` with `B` depending only on `r, N` is what yields the final `C/L` bound after
summing over the `L` sites.

This module proves that bound (Tasaki §6.2, eqs. (6.2.27)–(6.2.28), p. 164):
`‖M̂_x‖ ≤ B/L`, `B := π r (2r+1) N`.
The three ingredients are:

* **Per-site coefficient** `|(2π/L)·δ(x,y)| ≤ 2πr/L` for `y ∈ W_x` — the *centered* displacement
  `δ = signedRingDisp` has `|δ| = ringDist L x y ≤ r` (`natAbs_signedRingDisp_eq_ringDist`), so the
  raw linear angle's `2π` periodic-seam spread is avoided (this is the "slow-window" pitfall the
  centering resolves).
* **Per-site spin norm** `‖Ŝ_y^{(3)}‖ ≤ N/2` (`= S`, `onSiteS_spinSOp3_manyBodyOperatorNormS_le`).
* **Window cardinality** `|W_x| ≤ 2r+1` (`window_card_le`): the signed displacement injects `W_x`
  into `{−r, …, r}` (injectivity from `dvd_sub_signedRingDisp`, the range from
  `natAbs_signedRingDisp_eq_ringDist`).

Combined through the finite-sum triangle inequality and scalar homogeneity of the `L²` operator norm
`manyBodyOperatorNormS`, `‖M̂_x‖ ≤ (2r+1)·(2πr/L)·(N/2) = π r (2r+1) N / L`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, Lemma 6.4, eqs. (6.2.27)–(6.2.28), p. 164.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The **range-`r` window is small**: `|W_x| ≤ 2r+1` (Tasaki §6.2).  The signed cyclic displacement
`δ(x,·) = signedRingDisp L x ·` is injective on the window (two sites with equal displacement are
congruent modulo `L` by `dvd_sub_signedRingDisp`, hence equal in `Fin L`) and lands in the integer
interval `[−r, r]` (its magnitude is `ringDist ≤ r`), which has `2r+1` elements. -/
theorem window_card_le (L r : ℕ) (x : Fin L) : (window L r x).card ≤ 2 * r + 1 := by
  have hmaps : ∀ y ∈ window L r x, signedRingDisp L x y ∈ Finset.Icc (-(r : ℤ)) (r : ℤ) := by
    intro y hy
    have hrd : ringDist L x y ≤ r := (Finset.mem_filter.mp hy).2
    have habs : (signedRingDisp L x y).natAbs ≤ r := by
      rw [natAbs_signedRingDisp_eq_ringDist]; exact hrd
    rw [Finset.mem_Icc]; omega
  have hinj : Set.InjOn (signedRingDisp L x) (window L r x : Set (Fin L)) := by
    intro y₁ _ y₂ _ heq
    have hd1 := dvd_sub_signedRingDisp L x y₁
    have hd2 := dvd_sub_signedRingDisp L x y₂
    rw [heq] at hd1
    have hdvd : (L : ℤ) ∣ ((y₁.val : ℤ) - (y₂.val : ℤ)) := by
      have hs := dvd_sub hd1 hd2
      have hcalc : ((y₁.val : ℤ) - x.val - signedRingDisp L x y₂)
          - ((y₂.val : ℤ) - x.val - signedRingDisp L x y₂) = (y₁.val : ℤ) - (y₂.val : ℤ) := by ring
      rwa [hcalc] at hs
    have h1 : (y₁.val : ℤ) < L := by exact_mod_cast y₁.isLt
    have h2 : (y₂.val : ℤ) < L := by exact_mod_cast y₂.isLt
    have hzero : (y₁.val : ℤ) - (y₂.val : ℤ) = 0 := by
      by_contra hne
      have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hne
      omega
    exact Fin.ext (by omega)
  calc (window L r x).card
      ≤ (Finset.Icc (-(r : ℤ)) (r : ℤ)).card :=
        Finset.card_le_card_of_injOn (signedRingDisp L x) hmaps hinj
    _ = 2 * r + 1 := by rw [Int.card_Icc]; omega

/-- **The centered local twist generator norm bound** `‖M̂_x‖ ≤ B/L`, `B := π r (2r+1) N` (Tasaki
§6.2, eq. (6.2.27), p. 164).  By the finite-sum triangle inequality and scalar homogeneity of the
`L²` operator norm, `‖M̂_x‖ ≤ Σ_{y∈W_x} |(2π/L)δ(x,y)|·‖Ŝ_y^{(3)}‖`; each coefficient is
`≤ 2πr/L` (centered `|δ| = ringDist ≤ r`) and each `‖Ŝ_y^{(3)}‖ ≤ N/2`, over a window of
`≤ 2r+1` sites.  Uniform in `L`, this `O(1/L)` bound feeds the `O(‖M̂_x‖²)` second-order
twist-conjugation bound (PR-6/PR-7), whose sum over the `L` sites gives the Lemma 6.4 `C/L`. -/
theorem localTwistGen_manyBodyOperatorNormS_le (L N r : ℕ) (x : Fin L) (hL : 0 < L) :
    manyBodyOperatorNormS (localTwistGen L N r x)
      ≤ Real.pi * (r : ℝ) * (2 * (r : ℝ) + 1) * (N : ℝ) / (L : ℝ) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLR' : (L : ℝ) ≠ 0 := ne_of_gt hLR
  set c : ℝ := 2 * Real.pi * (r : ℝ) / (L : ℝ) * ((N : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hterm : ∀ y ∈ window L r x,
      manyBodyOperatorNormS
          ((((2 * Real.pi * (signedRingDisp L x y : ℝ)) / (L : ℝ) : ℝ) : ℂ) • spinSSiteOp3 y N)
        ≤ c := by
    intro y hy
    have hrd : ringDist L x y ≤ r := (Finset.mem_filter.mp hy).2
    rw [manyBodyOperatorNormS_smul, hc]
    refine mul_le_mul ?_ ?_ (manyBodyOperatorNormS_nonneg _) (by positivity)
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hLR, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      refine (div_le_div_iff_of_pos_right hLR).mpr ?_
      have hδ : |(signedRingDisp L x y : ℝ)| ≤ (r : ℝ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs, natAbs_signedRingDisp_eq_ringDist]
        exact_mod_cast hrd
      exact mul_le_mul_of_nonneg_left hδ (by positivity)
    · rw [spinSSiteOp3_def]; exact onSiteS_spinSOp3_manyBodyOperatorNormS_le y
  rw [localTwistGen]
  refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine le_trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast window_card_le L r x : ((window L r x).card : ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ))
    hc0) (le_of_eq ?_)
  rw [hc]; push_cast; field_simp

end LatticeSystem.Quantum
