import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateCoherentSecondMoment
import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateCoherentConcentration
import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateCoherentSecondMomentConcentration

/-!
# Tasaki §5.3 Theorem 5.3: final assembly of the `U(1)` symmetry-breaking limits (half-filling)

This module discharges the half-filling kernel of Theorem 5.3 as the theorem
`tasaki_5_3_bec_u1_ssb_half_filling` (predicate `IsBECCoherentSSBConstantsHalfFilling`).  It
assembles the coherent-state symmetry-breaking limits (5.3.6)–(5.3.8) from the **uniform
window-ratio concentration** carried by a realizing BEC coherent family
(`IsRealizingBECCoherentFamily`, `BoseEinsteinCondensateCoherentConcentration.lean`).

The genuine order parameter `m∗` is pinned per family: eventually every one-step off-diagonal ratio
`ρ_M = ⟨Γ_{M+1}, Ô⁺ Γ_M⟩ / L^d` in the (slow) window is within `ε` of `m∗`.  From this single
source:

* the coherent state is unit-normalized (`becCoherentState_self_eq_one`);
* the window average `(2 M_max + 1)^{-1} Σ ρ_M` converges to `m∗`
  (`becCoherent_ratioWindowAvg_sub_lt`), which drives the complex moments (5.3.6) and the axis means
  (5.3.7) — `⟨Ô^{(1)}⟩/L^d → m∗ cos θ`, `⟨Ô^{(2)}⟩/L^d → m∗ sin θ`, `⟨Ô^±⟩/L^d → m∗ e^{±iθ}`;
* the second moments (5.3.8) reduce to the same source via the band values `ρ_{M+1} ρ_M` (off-band)
  and `2 ρ_M²` + the elementary commutator residual `2M/L^{2d}` (diagonal, from the exact
  `Ô⁺Ô⁻ − Ô⁻Ô⁺ = 2 Ŝ³_tot`, `staggeredOrder_commutator`), giving
  `⟨(Ô^{(1)})²⟩/(L^d)² → (m∗ cos θ)²` and the `(2)` analogue.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.3, eqs. (5.3.5)–(5.3.8), pp. 141–142 (Koma–Tasaki [21]).
-/

namespace LatticeSystem.Quantum

open Matrix Filter Topology

open scoped ComplexOrder

/-! ### Normalization of the coherent state -/

/-- **Unit normalization of the coherent state** (Tasaki §5.3, eq. (5.3.5)): when the tower states
`Γ_M` are nonzero across the window `|M| ≤ M_max` (so each `Γ_M` is a genuine unit vector), the
`U(1)` coherent state `Ξ_θ` is unit-normalized, `⟨Ξ_θ, Ξ_θ⟩ = 1`.  The mutually orthogonal `Γ_M`
(distinct total-`Ŝ³` sectors, `towerState_unitNormalize_inner_eq_zero_of_ne`) contribute the
`2 M_max + 1` diagonal unit terms, cancelling the `(2 M_max + 1)^{-1}` normalization prefactor. -/
theorem becCoherentState_self_eq_one (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0)
    (hne : ∀ M : ℤ, -(Mmax : ℤ) ≤ M → M ≤ (Mmax : ℤ) →
        towerState (torusParitySublattice d L) 1 M Φ ≠ 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ becCoherentState d L θ Mmax Φ = 1 := by
  have horth : ∀ M M' : ℤ, M' ≠ M →
      star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
        (1 : Matrix (HypercubicTorus d L → Fin 2) (HypercubicTorus d L → Fin 2) ℂ).mulVec
          (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) = 0 := by
    intro M M' hne'
    rw [Matrix.one_mulVec]
    exact towerState_unitNormalize_inner_eq_zero_of_ne (torusParitySublattice d L)
      (Ne.symm hne') hsing
  have hcol := becCoherent_diagonal_collapse d L θ Mmax Φ 1 horth
  simp only [Matrix.one_mulVec] at hcol
  rw [hcol]
  have hdiag : ∀ M ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
      star (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) ⬝ᵥ
        unitNormalize (towerState (torusParitySublattice d L) 1 M Φ) = 1 := by
    intro M hM
    rw [Finset.mem_Icc] at hM
    have hpos : 0 < vecNormSqRe (towerState (torusParitySublattice d L) 1 M Φ) := by
      rw [vecNormSqRe]
      exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr (hne M hM.1 hM.2))).1
    exact unitNormalize_dotProduct_self _ hpos
  rw [Finset.sum_congr rfl hdiag, Finset.sum_const]
  have hcard : (Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ)).card = 2 * Mmax + 1 := by
    rw [Int.card_Icc]
    omega
  rw [hcard, nsmul_eq_mul]
  have hne1 : ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * (Mmax : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  rw [show ((2 * Mmax + 1 : ℕ) : ℂ) = ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ) from by push_cast; ring]
  field_simp

/-! ### Expectation ratios at the (normalized) coherent state -/

/-- With the coherent state unit-normalized, the real Rayleigh expectation is just the numerator's
real part. -/
theorem expectationRatioRe_becCoherent (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (O : Matrix (HypercubicTorus d L → Fin 2) (HypercubicTorus d L → Fin 2) ℂ)
    (hnorm : star (becCoherentState d L θ Mmax Φ) ⬝ᵥ becCoherentState d L θ Mmax Φ = 1) :
    expectationRatioRe O (becCoherentState d L θ Mmax Φ)
      = (star (becCoherentState d L θ Mmax Φ) ⬝ᵥ O.mulVec (becCoherentState d L θ Mmax Φ)).re := by
  rw [expectationRatioRe, hnorm, Complex.one_re, div_one]

/-- With the coherent state unit-normalized, the complex Rayleigh expectation is just the
numerator. -/
theorem expectationRatioComplex_becCoherent (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (O : Matrix (HypercubicTorus d L → Fin 2) (HypercubicTorus d L → Fin 2) ℂ)
    (hnorm : star (becCoherentState d L θ Mmax Φ) ⬝ᵥ becCoherentState d L θ Mmax Φ = 1) :
    expectationRatioComplex O (becCoherentState d L θ Mmax Φ)
      = star (becCoherentState d L θ Mmax Φ) ⬝ᵥ O.mulVec (becCoherentState d L θ Mmax Φ) := by
  rw [expectationRatioComplex, hnorm, div_one]

/-! ### Window-average concentration -/

/-- **Window-average concentration of the one-step ratios** (Tasaki §5.3, eq. (5.3.6)): under the
uniform window-ratio pinning of a realizing BEC coherent family (eventually every one-step ratio
`ρ_M = ⟨Γ_{M+1}, Ô⁺ Γ_M⟩ / L^d` is within `ε` of `m∗`) and a diverging window `M_win`, the Cesàro
window average `(2 M_win + 1)^{-1} Σ_{M ∈ [−M_win, M_win)} ρ_M` converges to `m∗`.  The window has
`2 M_win` terms against the `2 M_win + 1` normalization, so the average is
`(2 M_win + 1)^{-1}(Σ (ρ_M − m∗) − m∗)`; the pinned differences contribute `≤ ε/2` and the single
missing term `m∗ / (2 M_win + 1) → 0`. -/
theorem becCoherent_ratioWindowAvg_sub_lt (d : ℕ) (mStar : ℝ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (Mwin : ℕ → ℕ)
    (hwin : Tendsto Mwin atTop atTop)
    (hpin : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      ∀ M : ℤ, -(Mwin L : ℤ) ≤ M → M < (Mwin L : ℤ) →
        ‖(star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) (Φ L))) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
            / ((L : ℝ) ^ d : ℂ) - (mStar : ℂ)‖ < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      ‖((2 * (Mwin L : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
          ∑ M ∈ Finset.Ico (-(Mwin L : ℤ)) (Mwin L : ℤ),
            (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) (Φ L))) ⬝ᵥ
              (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
                (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
              / ((L : ℝ) ^ d : ℂ) - (mStar : ℂ)‖ < ε := by
  obtain ⟨L₀p, hp⟩ := hpin (ε / 2) (by linarith)
  obtain ⟨Kw, hKw⟩ : ∃ K : ℕ, 2 * |mStar| / ε < 2 * (K : ℝ) + 1 := by
    obtain ⟨K, hK⟩ := exists_nat_gt (2 * |mStar| / ε)
    exact ⟨K, by linarith [Nat.cast_nonneg (α := ℝ) K]⟩
  obtain ⟨L₀w, hw⟩ := Filter.eventually_atTop.mp (hwin.eventually_ge_atTop Kw)
  refine ⟨max L₀p L₀w, fun L _ hL h2 hev => ?_⟩
  have hMwinge : Kw ≤ Mwin L := hw L (le_trans (le_max_right _ _) hL)
  have hpL := hp L (le_trans (le_max_left _ _) hL) h2 hev
  set c : ℝ := 2 * (Mwin L : ℝ) + 1 with hc
  have hcpos : 0 < c := by positivity
  set win : Finset ℤ := Finset.Ico (-(Mwin L : ℤ)) (Mwin L : ℤ) with hwindef
  set g : ℤ → ℂ := fun M =>
    (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) (Φ L))) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
        / ((L : ℝ) ^ d : ℂ) with hg
  -- the average minus m∗ equals `c⁻¹ (Σ (g − m∗) − m∗)`
  have hcardZ : win.card = 2 * Mwin L := by rw [hwindef, Int.card_Ico]; omega
  have hcard : (win.card : ℂ) = (c : ℂ) - 1 := by rw [hcardZ, hc]; push_cast; ring
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hident : (c : ℂ)⁻¹ * (∑ M ∈ win, g M) - (mStar : ℂ)
      = (c : ℂ)⁻¹ * ((∑ M ∈ win, (g M - (mStar : ℂ))) - (mStar : ℂ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp
    ring
  have hnormc : ‖((c : ℝ) : ℂ)⁻¹‖ = c⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
  rw [hident, norm_mul, hnormc]
  -- bound `‖Σ (g − m∗) − m∗‖ ≤ (2 M_win)(ε/2) + |m∗|`
  have hsum : ‖(∑ M ∈ win, (g M - (mStar : ℂ)))‖ ≤ (win.card : ℝ) * (ε / 2) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ (fun M hM => ?_)
    rw [hwindef, Finset.mem_Ico] at hM
    exact le_of_lt (hpL M hM.1 hM.2)
  have hcard_real : (win.card : ℝ) = 2 * (Mwin L : ℝ) := by rw [hcardZ]; push_cast; ring
  have htri : ‖(∑ M ∈ win, (g M - (mStar : ℂ))) - (mStar : ℂ)‖
      ≤ 2 * (Mwin L : ℝ) * (ε / 2) + |mStar| := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hcard_real] at hsum
    linarith [hsum]
  -- combine: `c⁻¹ (2 M_win (ε/2) + |m∗|) < ε`
  have hMwin_lt : 2 * (Mwin L : ℝ) < c := by rw [hc]; linarith
  have hstar : |mStar| / c < ε / 2 := by
    rw [div_lt_div_iff₀ hcpos (by norm_num : (0:ℝ) < 2)]
    have hKwc : 2 * (Kw : ℝ) + 1 ≤ c := by
      rw [hc]; have : (Kw : ℝ) ≤ (Mwin L : ℝ) := by exact_mod_cast hMwinge
      linarith
    have : 2 * |mStar| < ε * c := by
      have h1 : 2 * |mStar| / ε < c := lt_of_lt_of_le hKw hKwc
      rw [div_lt_iff₀ hε] at h1; linarith
    linarith
  calc c⁻¹ * ‖(∑ M ∈ win, (g M - (mStar : ℂ))) - (mStar : ℂ)‖
      ≤ c⁻¹ * (2 * (Mwin L : ℝ) * (ε / 2) + |mStar|) := by
        apply mul_le_mul_of_nonneg_left htri (by positivity)
    _ = (2 * (Mwin L : ℝ) / c) * (ε / 2) + |mStar| / c := by field_simp
    _ < 1 * (ε / 2) + ε / 2 := by
        apply add_lt_add_of_le_of_lt
        · apply mul_le_mul_of_nonneg_right _ (by linarith)
          rw [div_le_one hcpos]; linarith
        · exact hstar
    _ = ε := by ring

/-! ### The first-order symmetry-breaking limits (eqs. (5.3.6), (5.3.7)) -/

/-- **Axis-`1` magnetization limit** (Tasaki §5.3, eq. (5.3.7)): for a realizing BEC coherent family
the coherent expectation `⟨Ξ_θ, Ô^{(1)} Ξ_θ⟩ / L^d` converges to `m∗ cos θ`.  From
`becCoherent_mean1` the expectation is `cos θ` times the window average of the one-step ratios
`r_M`, which converges to `m∗` by the uniform window-ratio concentration
(`becCoherent_ratioWindowAvg_sub_lt`). -/
private theorem becCoherent_mean1_limit (d : ℕ) (q₀ mStar C₁ : ℝ) (θ : ℝ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ) (Mwin : ℕ → ℕ)
    (hFam : IsRealizingBECCoherentFamily d q₀ mStar C₁ Φ E₀ Mwin) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      |expectationRatioRe (staggeredOrderOp1S (torusParitySublattice d L) 1)
          (becCoherentState d L θ (Mwin L) (Φ L)) / (L : ℝ) ^ d - mStar * Real.cos θ| < ε := by
  intro ε hε
  obtain ⟨L₂, hsec⟩ := becRealizing_eventually_sector d q₀ mStar C₁ Φ E₀ Mwin hFam
  obtain ⟨L₃, havg⟩ :=
    becCoherent_ratioWindowAvg_sub_lt d mStar Φ Mwin hFam.1.2.1 hFam.2.2.1 ε hε
  refine ⟨max L₂ L₃, fun L _ hL h2 hev => ?_⟩
  obtain ⟨hsing, hne⟩ := hsec L (le_trans (le_max_left _ _) hL) h2 hev
  have hclose := havg L (le_trans (le_max_right _ _) hL) h2 hev
  set A : ℂ := ((2 * (Mwin L : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
      ∑ M ∈ Finset.Ico (-(Mwin L : ℤ)) (Mwin L : ℤ),
        (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) (Φ L))) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
          / ((L : ℝ) ^ d : ℂ) with hA
  have hnorm := becCoherentState_self_eq_one d L θ (Mwin L) (Φ L) hsing hne
  have key : star (becCoherentState d L θ (Mwin L) (Φ L)) ⬝ᵥ
        (staggeredOrderOp1S (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ (Mwin L) (Φ L)) / ((L : ℝ) ^ d : ℂ)
      = (Real.cos θ : ℂ) * A := by
    rw [becCoherent_mean1 d L θ (Mwin L) (Φ L) hsing hne, hA, ← Finset.sum_div]
    ring
  rw [expectationRatioRe_becCoherent d L θ (Mwin L) (Φ L) _ hnorm, ← Complex.div_ofReal_re,
    Complex.ofReal_pow, key, Complex.re_ofReal_mul]
  calc |Real.cos θ * A.re - mStar * Real.cos θ|
      = |Real.cos θ| * |A.re - mStar| := by rw [← abs_mul]; ring_nf
    _ ≤ 1 * |A.re - mStar| :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (abs_nonneg _)
    _ = |(A - (mStar : ℂ)).re| := by rw [one_mul, Complex.sub_re, Complex.ofReal_re]
    _ ≤ ‖A - (mStar : ℂ)‖ := Complex.abs_re_le_norm _
    _ < ε := hclose

/-- **Axis-`2` magnetization limit** (Tasaki §5.3, eq. (5.3.7)): the coherent expectation
`⟨Ξ_θ, Ô^{(2)} Ξ_θ⟩ / L^d` converges to `m∗ sin θ`, via `becCoherent_mean2` (the `sin θ` companion
of `becCoherent_mean1`) and the same window-ratio concentration. -/
private theorem becCoherent_mean2_limit (d : ℕ) (q₀ mStar C₁ : ℝ) (θ : ℝ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ) (Mwin : ℕ → ℕ)
    (hFam : IsRealizingBECCoherentFamily d q₀ mStar C₁ Φ E₀ Mwin) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      |expectationRatioRe (staggeredOrderOp2S (torusParitySublattice d L) 1)
          (becCoherentState d L θ (Mwin L) (Φ L)) / (L : ℝ) ^ d - mStar * Real.sin θ| < ε := by
  intro ε hε
  obtain ⟨L₂, hsec⟩ := becRealizing_eventually_sector d q₀ mStar C₁ Φ E₀ Mwin hFam
  obtain ⟨L₃, havg⟩ :=
    becCoherent_ratioWindowAvg_sub_lt d mStar Φ Mwin hFam.1.2.1 hFam.2.2.1 ε hε
  refine ⟨max L₂ L₃, fun L _ hL h2 hev => ?_⟩
  obtain ⟨hsing, hne⟩ := hsec L (le_trans (le_max_left _ _) hL) h2 hev
  have hclose := havg L (le_trans (le_max_right _ _) hL) h2 hev
  set A : ℂ := ((2 * (Mwin L : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
      ∑ M ∈ Finset.Ico (-(Mwin L : ℤ)) (Mwin L : ℤ),
        (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) (Φ L))) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
          / ((L : ℝ) ^ d : ℂ) with hA
  have hnorm := becCoherentState_self_eq_one d L θ (Mwin L) (Φ L) hsing hne
  have key : star (becCoherentState d L θ (Mwin L) (Φ L)) ⬝ᵥ
        (staggeredOrderOp2S (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ (Mwin L) (Φ L)) / ((L : ℝ) ^ d : ℂ)
      = (Real.sin θ : ℂ) * A := by
    rw [becCoherent_mean2 d L θ (Mwin L) (Φ L) hsing hne, hA, ← Finset.sum_div]
    ring
  rw [expectationRatioRe_becCoherent d L θ (Mwin L) (Φ L) _ hnorm, ← Complex.div_ofReal_re,
    Complex.ofReal_pow, key, Complex.re_ofReal_mul]
  calc |Real.sin θ * A.re - mStar * Real.sin θ|
      = |Real.sin θ| * |A.re - mStar| := by rw [← abs_mul]; ring_nf
    _ ≤ 1 * |A.re - mStar| :=
        mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (abs_nonneg _)
    _ = |(A - (mStar : ℂ)).re| := by rw [one_mul, Complex.sub_re, Complex.ofReal_re]
    _ ≤ ‖A - (mStar : ℂ)‖ := Complex.abs_re_le_norm _
    _ < ε := hclose

/-- **Raising complex-moment limit** (Tasaki §5.3, eq. (5.3.6)): the complex coherent moment
`⟨Ξ_θ, Ô⁺ Ξ_θ⟩ / L^d` converges to `m∗ e^{iθ}`.  From `becCoherent_complexMoment_raising` it is
`e^{iθ}` times the window average of the one-step ratios, whose limit `m∗` is supplied by the
window-ratio concentration; `‖e^{iθ}‖ = 1` leaves the difference bounded by `‖A − m∗‖`. -/
private theorem becCoherent_complexRaising_limit (d : ℕ) (q₀ mStar C₁ : ℝ) (θ : ℝ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ) (Mwin : ℕ → ℕ)
    (hFam : IsRealizingBECCoherentFamily d q₀ mStar C₁ Φ E₀ Mwin) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      ‖expectationRatioComplex (staggeredRaisingOpS (torusParitySublattice d L) 1)
          (becCoherentState d L θ (Mwin L) (Φ L)) / ((L : ℝ) ^ d : ℂ)
        - (mStar : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ < ε := by
  intro ε hε
  obtain ⟨L₂, hsec⟩ := becRealizing_eventually_sector d q₀ mStar C₁ Φ E₀ Mwin hFam
  obtain ⟨L₃, havg⟩ :=
    becCoherent_ratioWindowAvg_sub_lt d mStar Φ Mwin hFam.1.2.1 hFam.2.2.1 ε hε
  refine ⟨max L₂ L₃, fun L _ hL h2 hev => ?_⟩
  obtain ⟨hsing, hne⟩ := hsec L (le_trans (le_max_left _ _) hL) h2 hev
  have hclose := havg L (le_trans (le_max_right _ _) hL) h2 hev
  set A : ℂ := ((2 * (Mwin L : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
      ∑ M ∈ Finset.Ico (-(Mwin L : ℤ)) (Mwin L : ℤ),
        (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) (Φ L))) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
          / ((L : ℝ) ^ d : ℂ) with hA
  have hnorm := becCoherentState_self_eq_one d L θ (Mwin L) (Φ L) hsing hne
  have key : star (becCoherentState d L θ (Mwin L) (Φ L)) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ (Mwin L) (Φ L)) / ((L : ℝ) ^ d : ℂ)
      = Complex.exp ((θ : ℂ) * Complex.I) * A := by
    rw [becCoherent_complexMoment_raising d L θ (Mwin L) (Φ L) hsing, hA, ← Finset.sum_div]
    ring
  rw [expectationRatioComplex_becCoherent d L θ (Mwin L) (Φ L) _ hnorm, key]
  have hexp : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  calc ‖Complex.exp ((θ : ℂ) * Complex.I) * A - (mStar : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖
      = ‖Complex.exp ((θ : ℂ) * Complex.I) * (A - (mStar : ℂ))‖ := by ring_nf
    _ = ‖A - (mStar : ℂ)‖ := by rw [norm_mul, hexp, one_mul]
    _ < ε := hclose

/-- **Lowering complex-moment limit** (Tasaki §5.3, eq. (5.3.6)): the complex coherent moment
`⟨Ξ_θ, Ô⁻ Ξ_θ⟩ / L^d` converges to `m∗ e^{−iθ}`.  From `becCoherent_complexMoment_lowering`, after
symmetrising the lowering window onto the raising window
(`becCoherent_loweringWindow_eq_raisingWindow`), it is `e^{−iθ}` times the same window average, with
limit `m∗`; `‖e^{−iθ}‖ = 1`. -/
private theorem becCoherent_complexLowering_limit (d : ℕ) (q₀ mStar C₁ : ℝ) (θ : ℝ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ) (Mwin : ℕ → ℕ)
    (hFam : IsRealizingBECCoherentFamily d q₀ mStar C₁ Φ E₀ Mwin) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      ‖expectationRatioComplex (staggeredLoweringOpS (torusParitySublattice d L) 1)
          (becCoherentState d L θ (Mwin L) (Φ L)) / ((L : ℝ) ^ d : ℂ)
        - (mStar : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)‖ < ε := by
  intro ε hε
  obtain ⟨L₂, hsec⟩ := becRealizing_eventually_sector d q₀ mStar C₁ Φ E₀ Mwin hFam
  obtain ⟨L₃, havg⟩ :=
    becCoherent_ratioWindowAvg_sub_lt d mStar Φ Mwin hFam.1.2.1 hFam.2.2.1 ε hε
  refine ⟨max L₂ L₃, fun L _ hL h2 hev => ?_⟩
  obtain ⟨hsing, hne⟩ := hsec L (le_trans (le_max_left _ _) hL) h2 hev
  have hclose := havg L (le_trans (le_max_right _ _) hL) h2 hev
  set A : ℂ := ((2 * (Mwin L : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
      ∑ M ∈ Finset.Ico (-(Mwin L : ℤ)) (Mwin L : ℤ),
        (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) (Φ L))) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
          / ((L : ℝ) ^ d : ℂ) with hA
  have hnorm := becCoherentState_self_eq_one d L θ (Mwin L) (Φ L) hsing hne
  have key : star (becCoherentState d L θ (Mwin L) (Φ L)) ⬝ᵥ
        (staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ (Mwin L) (Φ L)) / ((L : ℝ) ^ d : ℂ)
      = Complex.exp (-(θ : ℂ) * Complex.I) * A := by
    rw [becCoherent_complexMoment_lowering d L θ (Mwin L) (Φ L) hsing,
      becCoherent_loweringWindow_eq_raisingWindow d L (Mwin L) (Φ L) hne, hA, ← Finset.sum_div]
    ring
  rw [expectationRatioComplex_becCoherent d L θ (Mwin L) (Φ L) _ hnorm, key]
  have hexp : ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ = 1 := by
    rw [show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I from by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I (-θ)
  calc ‖Complex.exp (-(θ : ℂ) * Complex.I) * A - (mStar : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)‖
      = ‖Complex.exp (-(θ : ℂ) * Complex.I) * (A - (mStar : ℂ))‖ := by ring_nf
    _ = ‖A - (mStar : ℂ)‖ := by rw [norm_mul, hexp, one_mul]
    _ < ε := hclose

/-! ### The second-order symmetry-breaking limits (eq. (5.3.8)) -/

/-- **Triangle bound for a Hermitian-symmetric triple**: `‖X ± 2Y + conj X‖ ≤ 2‖X‖ + 2‖Y‖`. -/
private theorem becTriple_norm_le (X Y : ℂ) :
    ‖X + 2 * Y + star X‖ ≤ 2 * ‖X‖ + 2 * ‖Y‖
      ∧ ‖X - 2 * Y + star X‖ ≤ 2 * ‖X‖ + 2 * ‖Y‖ := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  refine ⟨?_, ?_⟩
  · calc ‖X + 2 * Y + star X‖ ≤ ‖X + 2 * Y‖ + ‖star X‖ := norm_add_le _ _
      _ ≤ (‖X‖ + ‖2 * Y‖) + ‖star X‖ := by gcongr; exact norm_add_le _ _
      _ = 2 * ‖X‖ + 2 * ‖Y‖ := by rw [norm_mul, h2, norm_star]; ring
  · calc ‖X - 2 * Y + star X‖ ≤ ‖X - 2 * Y‖ + ‖star X‖ := norm_add_le _ _
      _ ≤ (‖X‖ + ‖2 * Y‖) + ‖star X‖ := by gcongr; exact norm_sub_le _ _
      _ = 2 * ‖X‖ + 2 * ‖Y‖ := by rw [norm_mul, h2, norm_star]; ring

/-- **`cos 2θ`-representation of `cos²θ`**: `cos²θ = ¼(e^{2iθ} + 2 + e^{−2iθ})`. -/
private theorem becCos_sq_exp (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) ^ 2 = (4 : ℂ)⁻¹ *
      (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I) + 2
        + star (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I))) := by
  have hRe : (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I)).re = Real.cos (2 * θ) := by
    rw [show (((2 : ℤ) : ℝ) * θ * Complex.I) = ((2 * θ : ℝ) : ℂ) * Complex.I from by
      push_cast; ring, Complex.exp_ofReal_mul_I_re]
  have hsum : Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I) + 2
        + star (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I))
      = 2 * (((Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I)).re : ℝ) : ℂ) + 2 := by
    rw [Complex.star_def, show Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I) + 2
          + (starRingEnd ℂ) (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I))
        = (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I)
          + (starRingEnd ℂ) (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I))) + 2 from by ring,
      Complex.add_conj]
    push_cast; ring
  rw [hsum, hRe, show ((Real.cos θ : ℝ) : ℂ) ^ 2 = (((Real.cos θ) ^ 2 : ℝ) : ℂ) from by
    push_cast; ring, Real.cos_sq]
  push_cast; ring

/-- **`cos 2θ`-representation of `sin²θ`**: `sin²θ = −¼(e^{2iθ} − 2 + e^{−2iθ})`. -/
private theorem becSin_sq_exp (θ : ℝ) :
    ((Real.sin θ : ℝ) : ℂ) ^ 2 = (-(4 : ℂ)⁻¹) *
      (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I) - 2
        + star (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I))) := by
  have hRe : (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I)).re = Real.cos (2 * θ) := by
    rw [show (((2 : ℤ) : ℝ) * θ * Complex.I) = ((2 * θ : ℝ) : ℂ) * Complex.I from by
      push_cast; ring, Complex.exp_ofReal_mul_I_re]
  have hsum : Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I) - 2
        + star (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I))
      = 2 * (((Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I)).re : ℝ) : ℂ) - 2 := by
    rw [Complex.star_def, show Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I) - 2
          + (starRingEnd ℂ) (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I))
        = (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I)
          + (starRingEnd ℂ) (Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I))) - 2 from by ring,
      Complex.add_conj]
    push_cast; ring
  rw [hsum, hRe, show ((Real.sin θ : ℝ) : ℂ) ^ 2 = (((Real.sin θ) ^ 2 : ℝ) : ℂ) from by
    push_cast; ring, show (Real.sin θ) ^ 2 = 1 / 2 - Real.cos (2 * θ) / 2 from by
      rw [Real.sin_sq, Real.cos_two_mul]; ring]
  push_cast; ring

/-- **Conjugation of the `L^d`-scaled denominator is trivial** (real positive scale). -/
private theorem becStar_Vsq (L d : ℕ) : star (((L : ℝ) ^ d : ℂ) ^ 2) = ((L : ℝ) ^ d : ℂ) ^ 2 := by
  rw [show ((L : ℝ) ^ d : ℂ) ^ 2 = ((((L : ℝ) ^ d) ^ 2 : ℝ) : ℂ) from by push_cast; ring,
    Complex.star_def, Complex.conj_ofReal]

/-- **Axis-`1` squared-moment limit** (Tasaki §5.3, eq. (5.3.8)): the coherent second moment
`⟨Ξ_θ, (Ô^{(1)})² Ξ_θ⟩ / (L^d)²` converges to `(m∗ cos θ)²`.  Splitting `(Ô^{(1)})²` into the four
two-step bands (`becCoherent_secondMoment1_eq`), the diagonal `Ô⁺Ô⁻`, `Ô⁻Ô⁺` bands coincide
(`becCoherent_RL_eq_LR`) and the `Ô⁻Ô⁻` band conjugates `Ô⁺Ô⁺` (`becCoherent_LL_eq_conj_RR`), so
the moment is `¼(a + 2b + conj a)` with `a = ⟨Ô⁺Ô⁺⟩/(L^d)² → e^{2iθ} m∗²` (`becRR_moment_limit`)
and `b = ⟨Ô⁻Ô⁺⟩/(L^d)² → m∗²` (`becLR_moment_limit`); the trigonometric identity
`cos²θ = ¼(e^{2iθ} + 2 + e^{−2iθ})` (`becCos_sq_exp`) matches the limit to `(m∗ cos θ)²`. -/
private theorem becCoherent_secondMoment1_limit (d : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hC₁ : 0 < C₁)
    (θ : ℝ) (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ) (Mwin : ℕ → ℕ)
    (hFam : IsRealizingBECCoherentFamily d q₀ mStar C₁ Φ E₀ Mwin) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      |expectationRatioRe ((staggeredOrderOp1S (torusParitySublattice d L) 1) ^ 2)
          (becCoherentState d L θ (Mwin L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
        - (mStar * Real.cos θ) ^ 2| < ε := by
  intro ε hε
  obtain ⟨L₂, hsec⟩ := becRealizing_eventually_sector d q₀ mStar C₁ Φ E₀ Mwin hFam
  obtain ⟨LRR, hRR⟩ := becRR_moment_limit d q₀ mStar C₁ θ Φ E₀ Mwin hFam ε hε
  obtain ⟨LLR, hLR⟩ := becLR_moment_limit d hd q₀ mStar C₁ hC₁ θ Φ E₀ Mwin hFam ε hε
  refine ⟨max L₂ (max LRR LLR), fun L _ hL h2 hev => ?_⟩
  obtain ⟨hsingL, hneL⟩ := hsec L (le_trans (le_max_left _ _) hL) h2 hev
  have hnorm := becCoherentState_self_eq_one d L θ (Mwin L) (Φ L) hsingL hneL
  set Ξ := becCoherentState d L θ (Mwin L) (Φ L) with hΞ
  set P := Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I) with hPdef
  set a : ℂ := (star Ξ ⬝ᵥ (staggeredRaisingOpS (torusParitySublattice d L) 1
      * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec Ξ) / ((L : ℝ) ^ d : ℂ) ^ 2 with ha
  set b : ℂ := (star Ξ ⬝ᵥ (staggeredLoweringOpS (torusParitySublattice d L) 1
      * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec Ξ) / ((L : ℝ) ^ d : ℂ) ^ 2 with hb
  have hX : ‖a - P * (mStar : ℂ) ^ 2‖ < ε := hRR L (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hL)) h2 hev
  have hY : ‖b - (mStar : ℂ) ^ 2‖ < ε := hLR L (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hL)) h2 hev
  have hdiv : ∀ z : ℂ, star (z / ((L : ℝ) ^ d : ℂ) ^ 2) = star z / ((L : ℝ) ^ d : ℂ) ^ 2 := by
    intro z; rw [div_eq_mul_inv, star_mul', star_inv₀, becStar_Vsq, ← div_eq_mul_inv]
  have hcombine : (star Ξ ⬝ᵥ ((staggeredOrderOp1S (torusParitySublattice d L) 1) ^ 2).mulVec Ξ)
        / ((L : ℝ) ^ d : ℂ) ^ 2 = (4 : ℂ)⁻¹ * (a + 2 * b + star a) := by
    rw [becCoherent_secondMoment1_eq d L θ (Mwin L) (Φ L),
      becCoherent_RL_eq_LR d L θ (Mwin L) (Φ L) hsingL hneL,
      becCoherent_LL_eq_conj_RR d L θ (Mwin L) (Φ L), ha, hb, hdiv]
    ring
  rw [expectationRatioRe_becCoherent d L θ (Mwin L) (Φ L) _ hnorm, ← Complex.div_ofReal_re,
    show ((((L : ℝ) ^ d) ^ 2 : ℝ) : ℂ) = ((L : ℝ) ^ d : ℂ) ^ 2 from by push_cast; ring, hcombine]
  have htgt : ((mStar * Real.cos θ : ℝ) : ℂ) ^ 2
      = (4 : ℂ)⁻¹ * (P * (mStar : ℂ) ^ 2 + 2 * (mStar : ℂ) ^ 2 + star (P * (mStar : ℂ) ^ 2)) := by
    have hsm : star (P * (mStar : ℂ) ^ 2) = star P * (mStar : ℂ) ^ 2 := by
      rw [star_mul', star_pow, Complex.star_def, Complex.conj_ofReal, mul_comm]
    rw [hsm, show ((mStar * Real.cos θ : ℝ) : ℂ) ^ 2 = (mStar : ℂ) ^ 2 * ((Real.cos θ : ℝ) : ℂ) ^ 2
        from by push_cast; ring, becCos_sq_exp]
    ring
  have heq : (4 : ℂ)⁻¹ * (a + 2 * b + star a)
      - (4 : ℂ)⁻¹ * (P * (mStar : ℂ) ^ 2 + 2 * (mStar : ℂ) ^ 2 + star (P * (mStar : ℂ) ^ 2))
      = (4 : ℂ)⁻¹ * ((a - P * (mStar : ℂ) ^ 2) + 2 * (b - (mStar : ℂ) ^ 2)
          + star (a - P * (mStar : ℂ) ^ 2)) := by
    rw [star_sub]; ring
  rw [show (mStar * Real.cos θ) ^ 2 = (((mStar * Real.cos θ : ℝ) : ℂ) ^ 2).re from by
      rw [show ((mStar * Real.cos θ : ℝ) : ℂ) ^ 2 = (((mStar * Real.cos θ) ^ 2 : ℝ) : ℂ) from by
        push_cast; ring, Complex.ofReal_re], ← Complex.sub_re]
  refine lt_of_le_of_lt (Complex.abs_re_le_norm _) ?_
  rw [htgt, heq, norm_mul, show ‖(4 : ℂ)⁻¹‖ = 4⁻¹ from by rw [norm_inv]; norm_num]
  have htri := (becTriple_norm_le (a - P * (mStar : ℂ) ^ 2) (b - (mStar : ℂ) ^ 2)).1
  have : 4⁻¹ * ‖(a - P * (mStar : ℂ) ^ 2) + 2 * (b - (mStar : ℂ) ^ 2)
        + star (a - P * (mStar : ℂ) ^ 2)‖
      ≤ 4⁻¹ * (2 * ‖a - P * (mStar : ℂ) ^ 2‖ + 2 * ‖b - (mStar : ℂ) ^ 2‖) := by
    apply mul_le_mul_of_nonneg_left htri (by norm_num)
  refine lt_of_le_of_lt this ?_
  nlinarith [hX, hY]

/-- **Axis-`2` squared-moment limit** (Tasaki §5.3, eq. (5.3.8)): the coherent second moment
`⟨Ξ_θ, (Ô^{(2)})² Ξ_θ⟩ / (L^d)²` converges to `(m∗ sin θ)²`.  Mirror of
`becCoherent_secondMoment1_limit`: the sign-flipped split `−¼(a − 2b + conj a)`
(`becCoherent_secondMoment2_eq`) and `sin²θ = −¼(e^{2iθ} − 2 + e^{−2iθ})` (`becSin_sq_exp`). -/
private theorem becCoherent_secondMoment2_limit (d : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hC₁ : 0 < C₁)
    (θ : ℝ) (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ) (Mwin : ℕ → ℕ)
    (hFam : IsRealizingBECCoherentFamily d q₀ mStar C₁ Φ E₀ Mwin) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      |expectationRatioRe ((staggeredOrderOp2S (torusParitySublattice d L) 1) ^ 2)
          (becCoherentState d L θ (Mwin L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
        - (mStar * Real.sin θ) ^ 2| < ε := by
  intro ε hε
  obtain ⟨L₂, hsec⟩ := becRealizing_eventually_sector d q₀ mStar C₁ Φ E₀ Mwin hFam
  obtain ⟨LRR, hRR⟩ := becRR_moment_limit d q₀ mStar C₁ θ Φ E₀ Mwin hFam ε hε
  obtain ⟨LLR, hLR⟩ := becLR_moment_limit d hd q₀ mStar C₁ hC₁ θ Φ E₀ Mwin hFam ε hε
  refine ⟨max L₂ (max LRR LLR), fun L _ hL h2 hev => ?_⟩
  obtain ⟨hsingL, hneL⟩ := hsec L (le_trans (le_max_left _ _) hL) h2 hev
  have hnorm := becCoherentState_self_eq_one d L θ (Mwin L) (Φ L) hsingL hneL
  set Ξ := becCoherentState d L θ (Mwin L) (Φ L) with hΞ
  set P := Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I) with hPdef
  set a : ℂ := (star Ξ ⬝ᵥ (staggeredRaisingOpS (torusParitySublattice d L) 1
      * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec Ξ) / ((L : ℝ) ^ d : ℂ) ^ 2 with ha
  set b : ℂ := (star Ξ ⬝ᵥ (staggeredLoweringOpS (torusParitySublattice d L) 1
      * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec Ξ) / ((L : ℝ) ^ d : ℂ) ^ 2 with hb
  have hX : ‖a - P * (mStar : ℂ) ^ 2‖ < ε := hRR L (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hL)) h2 hev
  have hY : ‖b - (mStar : ℂ) ^ 2‖ < ε := hLR L (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) hL)) h2 hev
  have hdiv : ∀ z : ℂ, star (z / ((L : ℝ) ^ d : ℂ) ^ 2) = star z / ((L : ℝ) ^ d : ℂ) ^ 2 := by
    intro z; rw [div_eq_mul_inv, star_mul', star_inv₀, becStar_Vsq, ← div_eq_mul_inv]
  have hcombine : (star Ξ ⬝ᵥ ((staggeredOrderOp2S (torusParitySublattice d L) 1) ^ 2).mulVec Ξ)
        / ((L : ℝ) ^ d : ℂ) ^ 2 = (-(4 : ℂ)⁻¹) * (a - 2 * b + star a) := by
    rw [becCoherent_secondMoment2_eq d L θ (Mwin L) (Φ L),
      becCoherent_RL_eq_LR d L θ (Mwin L) (Φ L) hsingL hneL,
      becCoherent_LL_eq_conj_RR d L θ (Mwin L) (Φ L), ha, hb, hdiv]
    ring
  rw [expectationRatioRe_becCoherent d L θ (Mwin L) (Φ L) _ hnorm, ← Complex.div_ofReal_re,
    show ((((L : ℝ) ^ d) ^ 2 : ℝ) : ℂ) = ((L : ℝ) ^ d : ℂ) ^ 2 from by push_cast; ring, hcombine]
  have htgt : ((mStar * Real.sin θ : ℝ) : ℂ) ^ 2
      = (-(4 : ℂ)⁻¹)
        * (P * (mStar : ℂ) ^ 2 - 2 * (mStar : ℂ) ^ 2 + star (P * (mStar : ℂ) ^ 2)) := by
    have hsm : star (P * (mStar : ℂ) ^ 2) = star P * (mStar : ℂ) ^ 2 := by
      rw [star_mul', star_pow, Complex.star_def, Complex.conj_ofReal, mul_comm]
    rw [hsm, show ((mStar * Real.sin θ : ℝ) : ℂ) ^ 2 = (mStar : ℂ) ^ 2 * ((Real.sin θ : ℝ) : ℂ) ^ 2
        from by push_cast; ring, becSin_sq_exp]
    ring
  have heq : (-(4 : ℂ)⁻¹) * (a - 2 * b + star a)
      - (-(4 : ℂ)⁻¹) * (P * (mStar : ℂ) ^ 2 - 2 * (mStar : ℂ) ^ 2 + star (P * (mStar : ℂ) ^ 2))
      = (-(4 : ℂ)⁻¹) * ((a - P * (mStar : ℂ) ^ 2) - 2 * (b - (mStar : ℂ) ^ 2)
          + star (a - P * (mStar : ℂ) ^ 2)) := by
    rw [star_sub]; ring
  rw [show (mStar * Real.sin θ) ^ 2 = (((mStar * Real.sin θ : ℝ) : ℂ) ^ 2).re from by
      rw [show ((mStar * Real.sin θ : ℝ) : ℂ) ^ 2 = (((mStar * Real.sin θ) ^ 2 : ℝ) : ℂ) from by
        push_cast; ring, Complex.ofReal_re], ← Complex.sub_re]
  refine lt_of_le_of_lt (Complex.abs_re_le_norm _) ?_
  rw [htgt, heq, norm_mul, show ‖(-(4 : ℂ)⁻¹)‖ = 4⁻¹ from by rw [norm_neg, norm_inv]; norm_num]
  have htri := (becTriple_norm_le (a - P * (mStar : ℂ) ^ 2) (b - (mStar : ℂ) ^ 2)).2
  have : 4⁻¹ * ‖(a - P * (mStar : ℂ) ^ 2) - 2 * (b - (mStar : ℂ) ^ 2)
        + star (a - P * (mStar : ℂ) ^ 2)‖
      ≤ 4⁻¹ * (2 * ‖a - P * (mStar : ℂ) ^ 2‖ + 2 * ‖b - (mStar : ℂ) ^ 2‖) := by
    apply mul_le_mul_of_nonneg_left htri (by norm_num)
  refine lt_of_le_of_lt this ?_
  nlinarith [hX, hY]

/-! ### Theorem 5.3 (half-filling kernel): assembly of the `U(1)` symmetry-breaking limits -/

/-- **Tasaki Theorem 5.3, half-filling kernel (PROVED).**  Discharges the predicate
`IsBECCoherentSSBConstantsHalfFilling d q₀ C₁` (the `μ = 0` kernel of Theorem 5.3): for the `U(1)`
coherent state `Ξ_θ` built over the hard-core-boson tower, the order-operator density behaves as a
classical planar vector of length `m∗` in the direction `θ`, with vanishing fluctuation — the
first-order magnetization means `⟨Ô^{(1)}⟩/L^d → m∗ cos θ`, `⟨Ô^{(2)}⟩/L^d → m∗ sin θ`
(eq. (5.3.7)), the complex moments `⟨Ô^±⟩/L^d → m∗ e^{±iθ}` (eq. (5.3.6)), and the squared moments
`⟨(Ô^{(α)})²⟩/(L^d)² → (m∗ cos θ)² / (m∗ sin θ)²` (eq. (5.3.8)) — and `m∗ ≥ √(2 q₀)`.

The `hRealizing` hypothesis packages the Koma–Tasaki [21] uniform window-ratio concentration
(deferred with parity to the `SU(2)` sibling per the 2026-07-12 no-overreach boundary): it upgrades
any half-filling ODLRO ground-state family to a realizing BEC coherent family
(`IsRealizingBECCoherentFamily`) pinning the genuine order parameter `m∗`.  Given that, every SSB
limit is discharged axiom-free from the exact finite-`L` band collapses and the window
concentration, and `m∗ ≥ √(2 q₀)` is the documented axiom `becMStar_ge_sqrt_twoQ`; hence `#print
axioms` is
`std3 + becMStar_ge_sqrt_twoQ`.  Requires `d ≥ 2` (BEC long-range order, vacuous otherwise).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.3, eqs. (5.3.5)–(5.3.8), pp. 141–142 (Koma–Tasaki [21]). -/
theorem tasaki_5_3_bec_u1_ssb_half_filling (d : ℕ) (hd : 2 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hRealizing : ∀ (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ),
      (∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
        (xyChemicalPotentialHamiltonianS d L 0).mulVec (Φ L) = E₀ L • Φ L ∧
        (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin 2) → ℂ, Ψ ≠ 0 →
          (xyChemicalPotentialHamiltonianS d L 0).mulVec Ψ = E • Ψ → (E₀ L).re ≤ E.re) ∧
        Φ L ≠ 0 ∧
        (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec (Φ L) = 0 ∧
        (∀ α : Fin 3, α ≠ 2 → q₀ ≤ expectationRatioRe
          ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2) ∧
        (∀ M : ℤ, (M.natAbs : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
          towerState (torusParitySublattice d L) 1 M (Φ L) ≠ 0)) →
      ∃ mStar : ℝ, ∃ Mwin : ℕ → ℕ, IsRealizingBECCoherentFamily d q₀ mStar C₁ Φ E₀ Mwin) :
    ∃ C₁' : ℝ, IsBECCoherentSSBConstantsHalfFilling d q₀ C₁' := by
  refine ⟨C₁, hC₁, hq₀.le, fun θ Φ E₀ hbody => ?_⟩
  obtain ⟨mStar, Mwin, hFam⟩ := hRealizing Φ E₀ hbody
  refine ⟨mStar, hFam.2.2.2,
    becMStar_ge_sqrt_twoQ d (by omega) q₀ mStar C₁ hq₀ hC₁ Φ E₀ Mwin hFam, Mwin, hFam.1,
    becCoherent_mean1_limit d q₀ mStar C₁ θ Φ E₀ Mwin hFam,
    becCoherent_mean2_limit d q₀ mStar C₁ θ Φ E₀ Mwin hFam,
    becCoherent_secondMoment1_limit d (by omega) q₀ mStar C₁ hC₁ θ Φ E₀ Mwin hFam,
    becCoherent_secondMoment2_limit d (by omega) q₀ mStar C₁ hC₁ θ Φ E₀ Mwin hFam,
    becCoherent_complexRaising_limit d q₀ mStar C₁ θ Φ E₀ Mwin hFam,
    becCoherent_complexLowering_limit d q₀ mStar C₁ θ Φ E₀ Mwin hFam⟩

end LatticeSystem.Quantum
