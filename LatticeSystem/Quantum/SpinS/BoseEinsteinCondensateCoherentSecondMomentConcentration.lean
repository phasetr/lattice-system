import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateCoherentSecondMoment
import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateCoherentMoment
import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateCoherentConcentration
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundSU2

/-!
# Tasaki §5.3 Theorem 5.3: second-moment band values and their window concentration (eq. (5.3.8))

The exact finite-`L` band collapses of the coherent second moments (`becCoherent_secondMoment1_eq`
etc., `BoseEinsteinCondensateCoherentSecondMoment.lean`) leave four window band sums.  This module
evaluates those band sums and drives them to `m∗²` through the same uniform window-ratio
concentration used for the first moments:

* `becRatio_norm_le_two`: the one-step ratio `ρ_M = ⟨Γ_{M+1}, Ô⁺ Γ_M⟩ / L^d` is bounded by `2`
  (operator-norm Cauchy–Schwarz, `‖Ô⁺‖ ≤ 2 L^d`);
* `becTwoStepRaising_eq_ratio_prod`: on the two non-crossing branches (`M ≥ 0`, `M ≤ −2`) the
  two-step band element factors, `⟨Γ_{M+2}, Ô⁺Ô⁺ Γ_M⟩ = ⟨Γ_{M+2}, Ô⁺ Γ_{M+1}⟩ ⟨Γ_{M+1}, Ô⁺ Γ_M⟩`;
* the diagonal band `⟨Γ_M, Ô⁻Ô⁺ Γ_M⟩ = ‖Ô⁺ Γ_M‖²` reduces to `ρ_M²` (`M ≥ 0`) and, via the exact
  commutator `Ô⁺Ô⁻ − Ô⁻Ô⁺ = 2 Ŝ³` (`staggeredOrder_commutator`), the symmetric-window residual
  `Σ_M 2M = 0` cancels;
* the window averages `avg ρ_M²`, `avg ρ_{M+1} ρ_M` both tend to `m∗²`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.3, eq. (5.3.8), pp. 141–142 (Koma–Tasaki [21]).
-/

namespace LatticeSystem.Quantum

open Matrix Filter Topology

open scoped ComplexOrder InnerProductSpace

/-! ### Operator-norm bound on the one-step ratio -/

/-- **Modulus Cauchy–Schwarz** `‖⟨u, G v⟩‖ ≤ ‖G‖ ‖u‖₂ ‖v‖₂` (the complex-modulus companion of
`abs_re_dotProduct_mulVec_le_norm_mul`, dropping the real-part projection). -/
private theorem norm_star_dotProduct_mulVec_le {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (G : ManyBodyOpS Λ N) (u v : (Λ → Fin (N + 1)) → ℂ) :
    ‖star u ⬝ᵥ G.mulVec v‖
      ≤ manyBodyOperatorNormS G
          * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖
          * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ := by
  rw [manyBodyOperatorNormS_eq_toEuclideanCLM]
  have hbridge : star u ⬝ᵥ G.mulVec v
      = ⟪(WithLp.toLp 2 u : EuclideanSpace ℂ (Λ → Fin (N + 1))),
          Matrix.toEuclideanCLM (𝕜 := ℂ) G (WithLp.toLp 2 v)⟫_ℂ := by
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp]
    exact (dotProduct_comm _ _)
  rw [hbridge]
  calc ‖⟪(WithLp.toLp 2 u : EuclideanSpace ℂ (Λ → Fin (N + 1))),
            Matrix.toEuclideanCLM (𝕜 := ℂ) G (WithLp.toLp 2 v)⟫_ℂ‖
      ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖
          * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) G (WithLp.toLp 2 v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖
          * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) G‖
            * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖) := by
        gcongr
        exact (Matrix.toEuclideanCLM (𝕜 := ℂ) G).le_opNorm _
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℂ) G‖
          * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖
          * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ := by ring

/-- **Unit `L²` norm of a normalized vector**: `‖toLp 2 (unitNormalize w)‖ = 1` for `w ≠ 0`. -/
private theorem toLp_norm_unitNormalize_eq_one {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (w : (Λ → Fin (N + 1)) → ℂ) (hw : 0 < vecNormSqRe w) :
    ‖(WithLp.toLp 2 (unitNormalize w) : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ = 1 := by
  rw [← sqrt_vecNormSqRe_eq_toLp_norm]
  have h1 : vecNormSqRe (unitNormalize w) = 1 := by
    rw [vecNormSqRe, unitNormalize_dotProduct_self w hw, Complex.one_re]
  rw [h1, Real.sqrt_one]

/-- **Operator-norm bound of the staggered raising operator** on the torus: `‖Ô⁺‖ ≤ L^d`.  The
`torusParitySublattice`, `N = 1` specialization of `staggeredRaisingOpS_manyBodyOperatorNormS_le`,
using `Fintype.card (HypercubicTorus d L) = L^d`. -/
private theorem staggeredRaisingOpS_torus_norm_le (d L : ℕ) [NeZero L] :
    manyBodyOperatorNormS (staggeredRaisingOpS (torusParitySublattice d L) 1)
      ≤ (L : ℝ) ^ d := by
  have hcard : (Fintype.card (HypercubicTorus d L) : ℝ) = (L : ℝ) ^ d := by
    rw [card_hypercubicTorus]; push_cast; ring
  have h := staggeredRaisingOpS_manyBodyOperatorNormS_le (torusParitySublattice d L) (le_rfl)
  rw [hcard, Nat.cast_one, mul_one] at h
  exact h

/-- **Boundedness of the one-step ratio** (Tasaki §5.3): for nonzero neighbouring tower states, the
one-step off-diagonal ratio `ρ = ⟨Γ_{M'}, Ô⁺ Γ_M⟩ / L^d` obeys `‖ρ‖ ≤ 1`.  Operator-norm
Cauchy–Schwarz (`norm_star_dotProduct_mulVec_le`) with `‖Γ_{M'}‖ = ‖Γ_M‖ = 1` and `‖Ô⁺‖ ≤ L^d`. -/
theorem becRatio_norm_le_one (d L : ℕ) [NeZero L] {M M' : ℤ}
    {Φ : (HypercubicTorus d L → Fin 2) → ℂ}
    (ht : towerState (torusParitySublattice d L) 1 M Φ ≠ 0)
    (ht' : towerState (torusParitySublattice d L) 1 M' Φ ≠ 0) :
    ‖(star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)))
        / ((L : ℝ) ^ d : ℂ)‖ ≤ 1 := by
  have hposM : 0 < vecNormSqRe (towerState (torusParitySublattice d L) 1 M Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht)).1
  have hposM' : 0 < vecNormSqRe (towerState (torusParitySublattice d L) 1 M' Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht')).1
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hbound := norm_star_dotProduct_mulVec_le (staggeredRaisingOpS (torusParitySublattice d L) 1)
    (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ))
    (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ))
  rw [toLp_norm_unitNormalize_eq_one _ hposM', toLp_norm_unitNormalize_eq_one _ hposM,
    mul_one, mul_one] at hbound
  have hnum : ‖star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
      (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
        (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ))‖ ≤ (L : ℝ) ^ d :=
    le_trans hbound (staggeredRaisingOpS_torus_norm_le d L)
  have hden : ‖((L : ℝ) ^ d : ℂ)‖ = (L : ℝ) ^ d := by
    rw [show ((L : ℝ) ^ d : ℂ) = ((L : ℂ)) ^ d from by push_cast; ring, norm_pow,
      Complex.norm_natCast]
  rw [norm_div, hden, div_le_iff₀ hLd, one_mul]
  exact hnum

/-! ### Two-step raising-band factorization -/

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Raising parallel step** (`M ≥ 0`): on the raising side `Ô⁺ Γ_M` is parallel to `Γ_{M+1}`,
so it equals its `Γ_{M+1}`-component times `Γ_{M+1}`.  From the exact tower recursion
`Ô⁺ towerState M Φ = towerState (M+1) Φ` and the normalization scalars. -/
private theorem becRaising_uN_mulVec_eq_inner_smul (A : Λ → Bool) {M : ℤ} (hM : 0 ≤ M)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (ht' : towerState A N (M + 1) Φ ≠ 0) :
    (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ))
      = (star (unitNormalize (towerState A N (M + 1) Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ)))
        • unitNormalize (towerState A N (M + 1) Φ) := by
  have hD : 0 < vecNormSqRe (towerState A N (M + 1) Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht')).1
  have hne : ((Real.sqrt (vecNormSqRe (towerState A N (M + 1) Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hrec : (staggeredRaisingOpS A N).mulVec (towerState A N M Φ) = towerState A N (M + 1) Φ :=
    staggeredRaisingOpS_mulVec_towerState_of_nonneg A hM
  set sc : ℂ := (((Real.sqrt (vecNormSqRe (towerState A N M Φ)) : ℝ) : ℂ)⁻¹)
      * ((Real.sqrt (vecNormSqRe (towerState A N (M + 1) Φ)) : ℝ) : ℂ) with hsc
  have key : (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ))
      = sc • unitNormalize (towerState A N (M + 1) Φ) := by
    unfold unitNormalize
    rw [Matrix.mulVec_smul, hrec, smul_smul, hsc, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  rw [key, dotProduct_smul, unitNormalize_dotProduct_self _ hD, smul_eq_mul, mul_one]

/-- **Lowering parallel step** (`M ≤ 0`): mirror of `becRaising_uN_mulVec_eq_inner_smul`;
`Ô⁻ Γ_M` is parallel to `Γ_{M−1}`. -/
private theorem becLowering_uN_mulVec_eq_inner_smul (A : Λ → Bool) {M : ℤ} (hM : M ≤ 0)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (ht' : towerState A N (M - 1) Φ ≠ 0) :
    (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N M Φ))
      = (star (unitNormalize (towerState A N (M - 1) Φ)) ⬝ᵥ
          (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N M Φ)))
        • unitNormalize (towerState A N (M - 1) Φ) := by
  have hD : 0 < vecNormSqRe (towerState A N (M - 1) Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht')).1
  have hne : ((Real.sqrt (vecNormSqRe (towerState A N (M - 1) Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hrec : (staggeredLoweringOpS A N).mulVec (towerState A N M Φ) = towerState A N (M - 1) Φ :=
    staggeredLoweringOpS_mulVec_towerState_of_nonpos A hM
  set sc : ℂ := (((Real.sqrt (vecNormSqRe (towerState A N M Φ)) : ℝ) : ℂ)⁻¹)
      * ((Real.sqrt (vecNormSqRe (towerState A N (M - 1) Φ)) : ℝ) : ℂ) with hsc
  have key : (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N M Φ))
      = sc • unitNormalize (towerState A N (M - 1) Φ) := by
    unfold unitNormalize
    rw [Matrix.mulVec_smul, hrec, smul_smul, hsc, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  rw [key, dotProduct_smul, unitNormalize_dotProduct_self _ hD, smul_eq_mul, mul_one]

/-- **Two-step raising-band factorization, raising branch** (`M ≥ 0`, Tasaki §5.3, eq. (5.3.8)): the
`Ô⁺Ô⁺` band element factors into the product of the two consecutive one-step raising elements,
`⟨Γ_{M+2}, Ô⁺Ô⁺ Γ_M⟩ = ⟨Γ_{M+2}, Ô⁺ Γ_{M+1}⟩ ⟨Γ_{M+1}, Ô⁺ Γ_M⟩`.  Uses the raising parallel step to
replace `Ô⁺ Γ_M` by its `Γ_{M+1}`-component. -/
private theorem becTwoStepRaising_factor_nonneg (A : Λ → Bool) {M : ℤ} (hM : 0 ≤ M)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (ht1 : towerState A N (M + 1) Φ ≠ 0) :
    star (unitNormalize (towerState A N (M + 2) Φ)) ⬝ᵥ
        (staggeredRaisingOpS A N * staggeredRaisingOpS A N).mulVec
          (unitNormalize (towerState A N M Φ))
      = (star (unitNormalize (towerState A N (M + 2) Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N (M + 1) Φ)))
        * (star (unitNormalize (towerState A N (M + 1) Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ))) := by
  conv_lhs => rw [← Matrix.mulVec_mulVec, becRaising_uN_mulVec_eq_inner_smul A hM ht1,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

/-- **Two-step raising-band factorization, lowering branch** (`M ≤ −2`, Tasaki §5.3, eq. (5.3.8)):
same factorization on the lowering side, obtained by moving one `Ô⁺` onto the bra as `(Ô⁺)ᴴ = Ô⁻`
and using the lowering parallel step on `Ô⁻ Γ_{M+2}`. -/
private theorem becTwoStepRaising_factor_nonpos (A : Λ → Bool) {M : ℤ} (hM : M + 2 ≤ 0)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (ht1 : towerState A N (M + 1) Φ ≠ 0) :
    star (unitNormalize (towerState A N (M + 2) Φ)) ⬝ᵥ
        (staggeredRaisingOpS A N * staggeredRaisingOpS A N).mulVec
          (unitNormalize (towerState A N M Φ))
      = (star (unitNormalize (towerState A N (M + 2) Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N (M + 1) Φ)))
        * (star (unitNormalize (towerState A N (M + 1) Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ))) := by
  have ht1' : towerState A N ((M + 2) - 1) Φ ≠ 0 := by
    rwa [show (M + 2) - 1 = M + 1 from by ring]
  have hadj : star (unitNormalize (towerState A N (M + 2) Φ)) ⬝ᵥ
      (staggeredRaisingOpS A N).mulVec
        ((staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ)))
      = star ((staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N (M + 2) Φ))) ⬝ᵥ
        (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ)) := by
    rw [star_mulVec_dotProduct, staggeredLoweringOpS_conjTranspose]
  have hconj : star (star (unitNormalize (towerState A N (M + 1) Φ)) ⬝ᵥ
        (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N (M + 2) Φ)))
      = star (unitNormalize (towerState A N (M + 2) Φ)) ⬝ᵥ
        (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N (M + 1) Φ)) := by
    rw [Matrix.star_dotProduct, star_star, star_mulVec_dotProduct,
      staggeredLoweringOpS_conjTranspose]
  conv_lhs => rw [← Matrix.mulVec_mulVec, hadj,
    becLowering_uN_mulVec_eq_inner_smul A (show M + 2 ≤ 0 from hM) ht1',
    show (M + 2) - 1 = M + 1 from by ring, star_smul, smul_dotProduct, smul_eq_mul]
  rw [hconj]

/-! ### Generic window-average concentration -/

/-- **Generic Cesàro window-average concentration** (Tasaki §5.3, eq. (5.3.8) engine): if a complex
per-term value `v L M` is, eventually in `L`, within `ε` of a target `t` for every index in an index
set `I L` *outside* a bounded exceptional set `bad L` (`(bad L).card ≤ K`), is uniformly bounded
`‖v L M − t‖ ≤ B` on `I L`, and the index count `|I L|` stays within `K` of the normalization
`2 M_win L + 1`, then the normalized window average `(2 M_win L + 1)⁻¹ Σ_{I L} v L` tends to `t`.
The exceptional and count-defect terms are `O(K)` against the diverging `2 M_win L + 1`.  All the
per-term hypotheses and the conclusion are restricted to the "good" volumes `good L` (here
`2 ≤ L ∧ Even L`), so an odd-`L` or small-`L` value of `v` never has to satisfy the physics. -/
theorem becWindowAvg_of_termwise (Mwin : ℕ → ℕ) (hwin : Tendsto (fun L => (Mwin L : ℝ)) atTop atTop)
    (t : ℂ) (B : ℝ) (hB : 0 ≤ B) (K : ℕ) (good : ℕ → Prop)
    (v : ℕ → ℤ → ℂ) (I bad : ℕ → Finset ℤ)
    (hbadsub : ∀ L, good L → bad L ⊆ I L) (hbadcard : ∀ L, good L → (bad L).card ≤ K)
    (hcnt : ∀ L, good L → |((I L).card : ℝ) - (2 * (Mwin L : ℝ) + 1)| ≤ (K : ℝ))
    (hbdd : ∀ L, good L → ∀ M ∈ I L, ‖v L M - t‖ ≤ B)
    (hpin : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, good L → L₀ ≤ L →
      ∀ M ∈ I L, M ∉ bad L → ‖v L M - t‖ < ε) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L : ℕ, good L → L₀ ≤ L →
      ‖((2 * (Mwin L : ℝ) + 1 : ℝ) : ℂ)⁻¹ * (∑ M ∈ I L, v L M) - t‖ < ε := by
  obtain ⟨L₀p, hp⟩ := hpin (ε / 4) (by linarith)
  -- eventually `2 M_win + 1` dominates the `O(K)` remainders
  obtain ⟨L₀w, hw⟩ := Filter.eventually_atTop.mp
    (hwin.eventually_gt_atTop (max (K : ℝ) (4 * ((K : ℝ) * B + (K : ℝ) * ‖t‖ + 1) / ε)))
  refine ⟨max L₀p L₀w, fun L hgood hL => ?_⟩
  have hpL := hp L hgood (le_trans (le_max_left _ _) hL)
  have hMwin : max (K : ℝ) (4 * ((K : ℝ) * B + (K : ℝ) * ‖t‖ + 1) / ε) < (Mwin L : ℝ) :=
    hw L (le_trans (le_max_right _ _) hL)
  have hcK : (K : ℝ) < (Mwin L : ℝ) := lt_of_le_of_lt (le_max_left _ _) hMwin
  have hthr : 4 * ((K : ℝ) * B + (K : ℝ) * ‖t‖ + 1) < ε * (Mwin L : ℝ) := by
    have h1 : 4 * ((K : ℝ) * B + (K : ℝ) * ‖t‖ + 1) / ε < (Mwin L : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hMwin
    rw [div_lt_iff₀ hε] at h1
    linarith [h1]
  set c : ℝ := 2 * (Mwin L : ℝ) + 1 with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcard_le : ((I L).card : ℝ) ≤ c + K := by
    have h := abs_le.mp (hcnt L hgood); linarith [h.2]
  -- bound `‖Σ_I (v − t)‖ ≤ |I| (ε/4) + K B`
  have hsum : ‖∑ M ∈ I L, (v L M - t)‖ ≤ ((I L).card : ℝ) * (ε / 4) + (K : ℝ) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    have hsplit : ∑ M ∈ I L, ‖v L M - t‖
        = ∑ M ∈ I L \ bad L, ‖v L M - t‖ + ∑ M ∈ bad L, ‖v L M - t‖ := by
      rw [← Finset.sum_sdiff (hbadsub L hgood)]
    rw [hsplit]
    have hsumgood : ∑ M ∈ I L \ bad L, ‖v L M - t‖ ≤ ((I L).card : ℝ) * (ε / 4) := by
      refine le_trans (Finset.sum_le_card_nsmul _ _ (ε / 4) ?_) ?_
      · intro M hM
        rw [Finset.mem_sdiff] at hM
        exact le_of_lt (hpL M hM.1 hM.2)
      · rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
    have hbad : ∑ M ∈ bad L, ‖v L M - t‖ ≤ (K : ℝ) * B := by
      refine le_trans (Finset.sum_le_card_nsmul _ _ B ?_) ?_
      · intro M hM; exact hbdd L hgood M (hbadsub L hgood hM)
      · rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ hB
        exact_mod_cast hbadcard L hgood
    linarith
  -- assemble
  have hident : (c : ℂ)⁻¹ * (∑ M ∈ I L, v L M) - t
      = (c : ℂ)⁻¹ * ((∑ M ∈ I L, (v L M - t)) + (((I L).card : ℂ) - (c : ℂ)) * t) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    field_simp
    ring
  rw [hident, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
  have hcount : ‖((I L).card : ℂ) - (c : ℂ)‖ ≤ (K : ℝ) := by
    rw [show ((I L).card : ℂ) - (c : ℂ) = (((I L).card : ℝ) - c : ℝ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, hc]
    exact hcnt L hgood
  have htail : ‖(∑ M ∈ I L, (v L M - t)) + (((I L).card : ℂ) - (c : ℂ)) * t‖
      ≤ (((I L).card : ℝ) * (ε / 4) + (K : ℝ) * B) + (K : ℝ) * ‖t‖ := by
    refine le_trans (norm_add_le _ _) ?_
    have h2 : ‖(((I L).card : ℂ) - (c : ℂ)) * t‖ ≤ (K : ℝ) * ‖t‖ := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right hcount (norm_nonneg _)
    linarith [hsum, h2]
  have hfin : c⁻¹ * ((((I L).card : ℝ) * (ε / 4) + (K : ℝ) * B) + (K : ℝ) * ‖t‖) < ε := by
    rw [inv_mul_lt_iff₀ hcpos]
    have hKε : (K : ℝ) * ε < (Mwin L : ℝ) * ε := by
      apply mul_lt_mul_of_pos_right hcK hε
    nlinarith [hcard_le, hthr, hKε, hcpos, hε, hc]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left htail (by positivity)) hfin

/-! ### Uniform operator-norm bounds and diagonal band values -/

/-- **Operator-norm bound of the staggered lowering operator** on the torus: `‖Ô⁻‖ ≤ L^d` (mirror of
`staggeredRaisingOpS_torus_norm_le`). -/
private theorem staggeredLoweringOpS_torus_norm_le (d L : ℕ) [NeZero L] :
    manyBodyOperatorNormS (staggeredLoweringOpS (torusParitySublattice d L) 1)
      ≤ (L : ℝ) ^ d := by
  have hcard : (Fintype.card (HypercubicTorus d L) : ℝ) = (L : ℝ) ^ d := by
    rw [card_hypercubicTorus]; push_cast; ring
  have h := staggeredLoweringOpS_manyBodyOperatorNormS_le (torusParitySublattice d L) (le_rfl)
  rw [hcard, Nat.cast_one, mul_one] at h
  exact h

/-- **Operator-norm bound of a two-step product** on the torus: if `‖G‖ ≤ L^d` and `‖H‖ ≤ L^d` then
`‖G H‖ ≤ (L^d)²` (submultiplicativity `manyBodyOperatorNormS_mul_le`). -/
private theorem becProductOp_norm_le (d L : ℕ) [NeZero L]
    (G H : ManyBodyOpS (HypercubicTorus d L) 1)
    (hG : manyBodyOperatorNormS G ≤ (L : ℝ) ^ d) (hH : manyBodyOperatorNormS H ≤ (L : ℝ) ^ d) :
    manyBodyOperatorNormS (G * H) ≤ ((L : ℝ) ^ d) ^ 2 := by
  have hLd : (0 : ℝ) ≤ (L : ℝ) ^ d := by positivity
  calc manyBodyOperatorNormS (G * H)
      ≤ manyBodyOperatorNormS G * manyBodyOperatorNormS H := manyBodyOperatorNormS_mul_le G H
    _ ≤ (L : ℝ) ^ d * (L : ℝ) ^ d := mul_le_mul hG hH (manyBodyOperatorNormS_nonneg _) hLd
    _ = ((L : ℝ) ^ d) ^ 2 := by ring

/-- **Uniform bound on a two-step band element**: for nonzero tower states `Γ_a`, `Γ_b` and an
operator `P` with `‖P‖ ≤ (L^d)²`, the normalized band `⟨Γ_a, P Γ_b⟩` obeys `‖⟨Γ_a, P Γ_b⟩‖ ≤ (L^d)²`
(operator-norm Cauchy–Schwarz with unit `L²` norms). -/
private theorem becTwoStepBand_norm_le (d L : ℕ) [NeZero L] {a b : ℤ}
    {Φ : (HypercubicTorus d L → Fin 2) → ℂ}
    (hta : towerState (torusParitySublattice d L) 1 a Φ ≠ 0)
    (htb : towerState (torusParitySublattice d L) 1 b Φ ≠ 0)
    (P : ManyBodyOpS (HypercubicTorus d L) 1)
    (hP : manyBodyOperatorNormS P ≤ ((L : ℝ) ^ d) ^ 2) :
    ‖star (unitNormalize (towerState (torusParitySublattice d L) 1 a Φ)) ⬝ᵥ
        P.mulVec (unitNormalize (towerState (torusParitySublattice d L) 1 b Φ))‖
      ≤ ((L : ℝ) ^ d) ^ 2 := by
  have hposa : 0 < vecNormSqRe (towerState (torusParitySublattice d L) 1 a Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hta)).1
  have hposb : 0 < vecNormSqRe (towerState (torusParitySublattice d L) 1 b Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr htb)).1
  have hbound := norm_star_dotProduct_mulVec_le P
    (unitNormalize (towerState (torusParitySublattice d L) 1 a Φ))
    (unitNormalize (towerState (torusParitySublattice d L) 1 b Φ))
  rw [toLp_norm_unitNormalize_eq_one _ hposa, toLp_norm_unitNormalize_eq_one _ hposb,
    mul_one, mul_one] at hbound
  exact le_trans hbound hP

/-- **Product-closeness estimate**: if `x`, `y` are each within `δ` of the real target `a` and
`‖x‖ ≤ 1`, then `‖x y − a²‖ ≤ (1 + |a|) δ`.  The elementary two-term split
`x y − a² = x (y − a) + (x − a) a` behind the product concentration of every second-moment band. -/
private theorem becProd_close (x y : ℂ) (a δ : ℝ) (hx : ‖x - (a : ℂ)‖ ≤ δ)
    (hy : ‖y - (a : ℂ)‖ ≤ δ) (hxle : ‖x‖ ≤ 1) :
    ‖x * y - (a : ℂ) * (a : ℂ)‖ ≤ (1 + |a|) * δ := by
  have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hx
  have hsplit : x * y - (a : ℂ) * (a : ℂ) = x * (y - (a : ℂ)) + (x - (a : ℂ)) * (a : ℂ) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖x‖ * ‖y - (a : ℂ)‖ ≤ 1 * δ :=
    mul_le_mul hxle hy (norm_nonneg _) (by norm_num)
  have h2 : ‖x - (a : ℂ)‖ * |a| ≤ δ * |a| :=
    mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  nlinarith [h1, h2, abs_nonneg a, hδ]

/-- **Normalized total-`Ŝ³` eigenvector** (Tasaki §5.3): the normalized tower state `Γ_M` is a
`Ŝ³_tot`-eigenvector with eigenvalue `M` at half filling. -/
private theorem towerState_uN_totalSpin3_eigenvector (A : Λ → Bool) (M : ℤ)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    (totalSpinSOp3 Λ N).mulVec (unitNormalize (towerState A N M Φ))
      = (M : ℂ) • unitNormalize (towerState A N M Φ) := by
  unfold unitNormalize
  rw [Matrix.mulVec_smul, towerState_totalSpin3_eigenvector A M hsing, smul_comm]

/-- **Lowering band is the conjugate raising band** (Tasaki §5.3, eq. (5.3.3)): moving `Ô⁻` onto the
bra as `(Ô⁻)ᴴ = Ô⁺` turns `⟨Γ_a, Ô⁻ Γ_b⟩` into `conj ⟨Γ_b, Ô⁺ Γ_a⟩`. -/
private theorem becLoweringAdjoint_eq_conj_raising (A : Λ → Bool) {a b : ℤ}
    {Φ : (Λ → Fin (N + 1)) → ℂ} :
    star (unitNormalize (towerState A N a Φ)) ⬝ᵥ
        (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N b Φ))
      = star (star (unitNormalize (towerState A N b Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N a Φ))) := by
  have h : star (star (unitNormalize (towerState A N a Φ)) ⬝ᵥ
        (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N b Φ)))
      = star (unitNormalize (towerState A N b Φ)) ⬝ᵥ
        (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N a Φ)) := by
    rw [Matrix.star_dotProduct, star_star, star_mulVec_dotProduct,
      staggeredLoweringOpS_conjTranspose]
  rw [← h, star_star]

/-- **`Ô⁻Ô⁺` diagonal band on the raising side** (`M ≥ 0`, Tasaki §5.3, eq. (5.3.8)): the diagonal
band collapses to `c_M · conj c_M = ‖c_M‖²`, `c_M = ⟨Γ_{M+1}, Ô⁺ Γ_M⟩` (raising parallel step, then
`⟨Γ_M, Ô⁻ Γ_{M+1}⟩ = conj c_M`). -/
private theorem becLR_band_clean (A : Λ → Bool) {M : ℤ} (hM : 0 ≤ M)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (ht1 : towerState A N (M + 1) Φ ≠ 0) :
    star (unitNormalize (towerState A N M Φ)) ⬝ᵥ
        (staggeredLoweringOpS A N * staggeredRaisingOpS A N).mulVec
          (unitNormalize (towerState A N M Φ))
      = (star (unitNormalize (towerState A N (M + 1) Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ)))
        * star (star (unitNormalize (towerState A N (M + 1) Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ))) := by
  set c := star (unitNormalize (towerState A N (M + 1) Φ)) ⬝ᵥ
    (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N M Φ)) with hc
  have h : (staggeredLoweringOpS A N * staggeredRaisingOpS A N).mulVec
        (unitNormalize (towerState A N M Φ))
      = c • (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N (M + 1) Φ)) := by
    rw [← Matrix.mulVec_mulVec, becRaising_uN_mulVec_eq_inner_smul A hM ht1, Matrix.mulVec_smul,
      ← hc]
  rw [h, dotProduct_smul, smul_eq_mul, becLoweringAdjoint_eq_conj_raising A, ← hc]

/-- **`Ô⁺Ô⁻` diagonal band on the lowering side** (`M ≤ 0`, Tasaki §5.3, eq. (5.3.8)): the diagonal
band collapses to `conj c_{M-1} · c_{M-1} = ‖c_{M-1}‖²`, `c_{M-1} = ⟨Γ_M, Ô⁺ Γ_{M-1}⟩` (lowering
parallel step, then `⟨Γ_{M-1}, Ô⁻ Γ_M⟩ = conj c_{M-1}`). -/
private theorem becRL_band_clean (A : Λ → Bool) {M : ℤ} (hM : M ≤ 0)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (ht1 : towerState A N (M - 1) Φ ≠ 0) :
    star (unitNormalize (towerState A N M Φ)) ⬝ᵥ
        (staggeredRaisingOpS A N * staggeredLoweringOpS A N).mulVec
          (unitNormalize (towerState A N M Φ))
      = star (star (unitNormalize (towerState A N M Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N (M - 1) Φ)))
        * (star (unitNormalize (towerState A N M Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N (M - 1) Φ))) := by
  set cc := star (unitNormalize (towerState A N M Φ)) ⬝ᵥ
    (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N (M - 1) Φ)) with hcc
  set c' := star (unitNormalize (towerState A N (M - 1) Φ)) ⬝ᵥ
    (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N M Φ)) with hc'
  have h : (staggeredRaisingOpS A N * staggeredLoweringOpS A N).mulVec
        (unitNormalize (towerState A N M Φ))
      = c' • (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N (M - 1) Φ)) := by
    rw [← Matrix.mulVec_mulVec, becLowering_uN_mulVec_eq_inner_smul A hM ht1, Matrix.mulVec_smul,
      ← hc']
  rw [h, dotProduct_smul, smul_eq_mul, hc', becLoweringAdjoint_eq_conj_raising A, ← hcc]

/-- **Commutator relation between the diagonal bands** (Tasaki §5.3, eq. (4.2.32)): at half filling
the `Ô⁻Ô⁺` diagonal band is the `Ô⁺Ô⁻` diagonal band minus `2M`, from `[Ô⁺, Ô⁻] = 2 Ŝ³_tot`
(`staggeredOrder_commutator`) and `Ŝ³_tot Γ_M = M Γ_M`. -/
private theorem becLR_eq_RL_sub_two (A : Λ → Bool) (M : ℤ)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (ht : towerState A N M Φ ≠ 0) :
    star (unitNormalize (towerState A N M Φ)) ⬝ᵥ
        (staggeredLoweringOpS A N * staggeredRaisingOpS A N).mulVec
          (unitNormalize (towerState A N M Φ))
      = star (unitNormalize (towerState A N M Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N * staggeredLoweringOpS A N).mulVec
            (unitNormalize (towerState A N M Φ)) - 2 * (M : ℂ) := by
  have hpos : 0 < vecNormSqRe (towerState A N M Φ) := by
    rw [vecNormSqRe]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr ht)).1
  have hcomm : staggeredRaisingOpS A N * staggeredLoweringOpS A N
      - staggeredLoweringOpS A N * staggeredRaisingOpS A N = (2 : ℂ) • totalSpinSOp3 Λ N :=
    staggeredOrder_commutator A
  have key : star (unitNormalize (towerState A N M Φ)) ⬝ᵥ
        (staggeredLoweringOpS A N * staggeredRaisingOpS A N).mulVec
          (unitNormalize (towerState A N M Φ))
      = star (unitNormalize (towerState A N M Φ)) ⬝ᵥ
          (staggeredRaisingOpS A N * staggeredLoweringOpS A N).mulVec
            (unitNormalize (towerState A N M Φ))
        - star (unitNormalize (towerState A N M Φ)) ⬝ᵥ
          ((2 : ℂ) • totalSpinSOp3 Λ N).mulVec (unitNormalize (towerState A N M Φ)) := by
    rw [← hcomm, Matrix.sub_mulVec, dotProduct_sub]; ring
  rw [key]
  congr 1
  rw [Matrix.smul_mulVec, towerState_uN_totalSpin3_eigenvector A M hsing, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, unitNormalize_dotProduct_self _ hpos]
  ring

/-! ### Eventual half-filling and window nonvanishing from a realizing family -/

/-- **Eventual half-filling with nonvanishing tower states across the window** (Tasaki §5.3): a
realizing BEC coherent family is, eventually in even `L`, at half filling (`Ŝ³_tot Φ = 0`) with each
tower state in the closed window `|M| ≤ M_win` nonzero.  The half-filling and nonvanishing come from
the family body; the window inclusion uses the slow-window bound `M_win L ≤ C₁ L^{d/2}`. -/
theorem becRealizing_eventually_sector (d : ℕ) (q₀ mStar C₁ : ℝ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ) (Mwin : ℕ → ℕ)
    (hFam : IsRealizingBECCoherentFamily d q₀ mStar C₁ Φ E₀ Mwin) :
    ∃ L₂ : ℕ, ∀ (L : ℕ) [NeZero L], L₂ ≤ L → 2 ≤ L → Even L →
      (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec (Φ L) = 0 ∧
      ∀ M : ℤ, -(Mwin L : ℤ) ≤ M → M ≤ (Mwin L : ℤ) →
        towerState (torusParitySublattice d L) 1 M (Φ L) ≠ 0 := by
  obtain ⟨L₁, hbody⟩ := hFam.2.1
  obtain ⟨Ls, hLs⟩ := Filter.eventually_atTop.mp hFam.1.2.2
  refine ⟨max L₁ Ls, fun L _ hL h2 hev => ?_⟩
  obtain ⟨_, _, _, hsing, _, hnz⟩ := hbody L (le_trans (le_max_left _ _) hL) h2 hev
  refine ⟨hsing, fun M hM1 hM2 => hnz M ?_⟩
  have hbound : (Mwin L : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) :=
    hLs L (le_trans (le_max_right _ _) hL)
  have hnat : (M.natAbs : ℝ) ≤ (Mwin L : ℝ) := by
    have : M.natAbs ≤ Mwin L := by omega
    exact_mod_cast this
  linarith

/-! ### Concentration of the off-diagonal `Ô⁺Ô⁺` band (raising–raising, phase `e^{2iθ}`) -/

/-- **Raising–raising second-moment concentration** (Tasaki §5.3, eq. (5.3.8)): for a realizing BEC
coherent family the coherent expectation `⟨Ξ_θ, Ô⁺Ô⁺ Ξ_θ⟩ / (L^d)²` converges to
`e^{2iθ} m∗²`.  The `+2`-band collapses (`becCoherent_raisingRaising_collapse`) to a phase times the
window average of the two-step products `⟨Γ_{M+2}, Ô⁺Ô⁺ Γ_M⟩ = ρ_{M+1} ρ_M`
(`becTwoStepRaising_factor`), and each product concentrates on `m∗²` by the uniform window-ratio
pinning (`becProd_close`), the exceptional index `M = −1` (neither factorization branch) forming a
bounded bad set. -/
theorem becRR_moment_limit (d : ℕ) (q₀ mStar C₁ : ℝ) (θ : ℝ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ) (Mwin : ℕ → ℕ)
    (hFam : IsRealizingBECCoherentFamily d q₀ mStar C₁ Φ E₀ Mwin) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      ‖(star (becCoherentState d L θ (Mwin L) (Φ L)) ⬝ᵥ
          (staggeredRaisingOpS (torusParitySublattice d L) 1
            * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
            (becCoherentState d L θ (Mwin L) (Φ L)))
          / ((L : ℝ) ^ d : ℂ) ^ 2
        - Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I) * (mStar : ℂ) ^ 2‖ < ε := by
  intro ε hε
  obtain ⟨L₂, hsec⟩ := becRealizing_eventually_sector d q₀ mStar C₁ Φ E₀ Mwin hFam
  have hmStar : 0 < mStar := hFam.2.2.2
  -- window and exceptional sets
  set I : ℕ → Finset ℤ := fun L =>
    (Finset.Icc (-(Mwin L : ℤ)) (Mwin L : ℤ)).filter
      (fun M => -(Mwin L : ℤ) ≤ M + 2 ∧ M + 2 ≤ (Mwin L : ℤ)) with hI
  set bad : ℕ → Finset ℤ := fun L => (I L).filter (fun M => M = -1) with hbad
  set v : ℕ → ℤ → ℂ := fun L M =>
    if h : 2 ≤ L ∧ Even L then
      letI : NeZero L := ⟨by have := h.1; omega⟩
      (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 2) (Φ L))) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
        / ((L : ℝ) ^ d : ℂ) ^ 2
    else (mStar : ℂ) ^ 2 with hv
  have hIeq : ∀ L, I L = Finset.Icc (-(Mwin L : ℤ)) ((Mwin L : ℤ) - 2) := by
    intro L; rw [hI]; ext M; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  -- engine hypotheses
  have hbadsub : ∀ L, (2 ≤ L ∧ Even L) → bad L ⊆ I L := fun L _ => Finset.filter_subset _ _
  have hbadcard : ∀ L, (2 ≤ L ∧ Even L) → (bad L).card ≤ 2 := by
    intro L _
    refine le_trans (Finset.card_le_card (show bad L ⊆ {(-1 : ℤ)} from ?_)) (by norm_num)
    intro x hx; rw [hbad, Finset.mem_filter] at hx; simp [hx.2]
  have hcnt : ∀ L, (2 ≤ L ∧ Even L) →
      |((I L).card : ℝ) - (2 * (Mwin L : ℝ) + 1)| ≤ ((2 : ℕ) : ℝ) := by
    intro L _
    have hc : (I L).card ≤ 2 * Mwin L + 1 ∧ 2 * Mwin L + 1 ≤ (I L).card + 2 := by
      rw [hIeq, Int.card_Icc]; omega
    have hc1 : ((I L).card : ℝ) ≤ 2 * (Mwin L : ℝ) + 1 := by exact_mod_cast hc.1
    have hc2 : 2 * (Mwin L : ℝ) + 1 ≤ ((I L).card : ℝ) + 2 := by exact_mod_cast hc.2
    rw [abs_le]; push_cast; constructor <;> linarith
  have hBnn : (0 : ℝ) ≤ 1 + mStar ^ 2 := by positivity
  have hbdd : ∀ L, (2 ≤ L ∧ Even L) → ∀ M ∈ I L,
      ‖v L M - (mStar : ℂ) ^ 2‖ ≤ 1 + mStar ^ 2 := by
    intro L hgood M _
    haveI : NeZero L := ⟨by have := hgood.1; omega⟩
    have hvnorm : ‖v L M‖ ≤ 1 := by
      rw [hv]; simp only [dif_pos hgood]
      by_cases hz : towerState (torusParitySublattice d L) 1 (M + 2) (Φ L) = 0 ∨
          towerState (torusParitySublattice d L) 1 M (Φ L) = 0
      · have hnum0 : (star (unitNormalize
            (towerState (torusParitySublattice d L) 1 (M + 2) (Φ L))) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1
              * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L)))) = 0 := by
          rcases hz with hz | hz <;> simp [hz, unitNormalize]
        rw [hnum0, zero_div, norm_zero]; norm_num
      · rw [not_or] at hz
        have hLd : (0 : ℝ) < (L : ℝ) ^ d := by
          have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
          positivity
        have hden : ‖((L : ℝ) ^ d : ℂ) ^ 2‖ = ((L : ℝ) ^ d) ^ 2 := by
          rw [norm_pow, show ((L : ℝ) ^ d : ℂ) = ((L : ℂ)) ^ d from by push_cast; ring, norm_pow,
            Complex.norm_natCast]
        have hnum := becTwoStepBand_norm_le d L hz.1 hz.2
          (staggeredRaisingOpS (torusParitySublattice d L) 1
            * staggeredRaisingOpS (torusParitySublattice d L) 1)
          (becProductOp_norm_le d L _ _ (staggeredRaisingOpS_torus_norm_le d L)
            (staggeredRaisingOpS_torus_norm_le d L))
        rw [norm_div, hden, div_le_one (by positivity)]
        exact hnum
    have h2m : ‖(mStar : ℂ) ^ 2‖ = mStar ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
    calc ‖v L M - (mStar : ℂ) ^ 2‖ ≤ ‖v L M‖ + ‖(mStar : ℂ) ^ 2‖ := norm_sub_le _ _
      _ ≤ 1 + mStar ^ 2 := by rw [h2m]; linarith
  have hpin : ∀ ε' : ℝ, 0 < ε' → ∃ L₀ : ℕ, ∀ L : ℕ, (2 ≤ L ∧ Even L) → L₀ ≤ L →
      ∀ M ∈ I L, M ∉ bad L → ‖v L M - (mStar : ℂ) ^ 2‖ < ε' := by
    intro ε' hε'
    obtain ⟨Lp, hp⟩ := hFam.2.2.1 (ε' / (2 * (1 + mStar))) (by positivity)
    refine ⟨max L₂ Lp, fun L hgood hL M hMI hMbad => ?_⟩
    haveI : NeZero L := ⟨by have := hgood.1; omega⟩
    obtain ⟨hsingL, hneL⟩ := hsec L (le_trans (le_max_left _ _) hL) hgood.1 hgood.2
    have hMne : M ≠ -1 := by
      intro hM1; exact hMbad (by rw [hbad, Finset.mem_filter]; exact ⟨hMI, hM1⟩)
    rw [hIeq, Finset.mem_Icc] at hMI
    -- nonvanishing of the three neighbouring tower states
    have ht0 := hneL M (by omega) (by omega)
    have ht1 := hneL (M + 1) (by omega) (by omega)
    have ht2 := hneL (M + 2) (by omega) (by omega)
    have hLdC : ((L : ℝ) ^ d : ℂ) ≠ 0 := by
      have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      have hpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
      exact_mod_cast hpos.ne'
    -- band factorization `⟨Γ_{M+2}, Ô⁺Ô⁺ Γ_M⟩ = c_{M+1} c_M`
    have hfac : star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 2) (Φ L))) ⬝ᵥ
          (staggeredRaisingOpS (torusParitySublattice d L) 1
            * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
            (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L)))
        = (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 2) (Φ L))) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) (Φ L))))
          * (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) (Φ L))) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L)))) := by
      by_cases hM0 : (0 : ℤ) ≤ M
      · exact becTwoStepRaising_factor_nonneg (torusParitySublattice d L) hM0 ht1
      · exact becTwoStepRaising_factor_nonpos (torusParitySublattice d L) (by omega) ht1
    -- pinning of the two factor ratios
    have hpM := hp L (le_trans (le_max_right _ _) hL) hgood.1 hgood.2 M (by omega) (by omega)
    have hpM1 := hp L (le_trans (le_max_right _ _) hL) hgood.1 hgood.2 (M + 1) (by omega) (by omega)
    rw [show ((M : ℤ) + 1 + 1) = M + 2 from by ring] at hpM1
    have hxle : ‖(star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 2) (Φ L))) ⬝ᵥ
          (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
            (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) (Φ L))))
          / ((L : ℝ) ^ d : ℂ)‖ ≤ 1 := becRatio_norm_le_one d L ht1 ht2
    have hclose := becProd_close _ _ mStar (ε' / (2 * (1 + mStar))) hpM1.le hpM.le hxle
    -- rewrite `v L M` and finish
    rw [hv]; simp only [dif_pos hgood]
    rw [hfac, show ((L : ℝ) ^ d : ℂ) ^ 2 = ((L : ℝ) ^ d : ℂ) * ((L : ℝ) ^ d : ℂ) from by ring,
      mul_div_mul_comm, sq]
    refine lt_of_le_of_lt hclose ?_
    rw [abs_of_pos hmStar]
    have hδ : (1 + mStar) * (ε' / (2 * (1 + mStar))) = ε' / 2 := by
      rw [mul_div_assoc']; field_simp
    rw [hδ]; linarith
  -- run the engine and bridge to the collapsed expectation
  obtain ⟨L₀, hL₀⟩ := becWindowAvg_of_termwise Mwin
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hFam.1.2.1)
    ((mStar : ℂ) ^ 2) (1 + mStar ^ 2) hBnn 2 (fun L => 2 ≤ L ∧ Even L) v I bad
    hbadsub hbadcard hcnt hbdd hpin ε hε
  refine ⟨max L₀ L₂, fun L _ hL h2 hev => ?_⟩
  have hgood : 2 ≤ L ∧ Even L := ⟨h2, hev⟩
  obtain ⟨hsingL, _⟩ := hsec L (le_trans (le_max_right _ _) hL) h2 hev
  have hkey := hL₀ L hgood (le_trans (le_max_left _ _) hL)
  have hSum : ∑ M ∈ I L, v L M
      = (∑ M ∈ (Finset.Icc (-(Mwin L : ℤ)) (Mwin L : ℤ)).filter
            (fun M => -(Mwin L : ℤ) ≤ M + 2 ∧ M + 2 ≤ (Mwin L : ℤ)),
          star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 2) (Φ L))) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1
              * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
        / ((L : ℝ) ^ d : ℂ) ^ 2 := by
    rw [Finset.sum_div, hI]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [hv]; simp only [dif_pos hgood]
  have hbridge : (star (becCoherentState d L θ (Mwin L) (Φ L)) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ (Mwin L) (Φ L)))
        / ((L : ℝ) ^ d : ℂ) ^ 2
      = Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I) *
        (((2 * (Mwin L : ℝ) + 1 : ℝ) : ℂ)⁻¹ * ∑ M ∈ I L, v L M) := by
    rw [becCoherent_raisingRaising_collapse d L θ (Mwin L) (Φ L) hsingL, hSum]
    ring
  rw [hbridge, ← mul_sub, norm_mul]
  have hph : ‖Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I)‖ = 1 := by
    rw [show (((2 : ℤ) : ℝ) * θ * Complex.I) = (((2 : ℤ) : ℝ) * θ : ℝ) * Complex.I from by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hph, one_mul]
  exact hkey

/-! ### Concentration of the diagonal `Ô⁻Ô⁺` band (phase `1`) -/

/-- **Conjugate of a real-denominator ratio**: `conj (z / L^d) = conj z / L^d` (the denominator is a
positive real, fixed by conjugation). -/
private theorem becStar_ratio (num : ℂ) (L d : ℕ) :
    star (num / ((L : ℝ) ^ d : ℂ)) = star num / ((L : ℝ) ^ d : ℂ) := by
  have hden : star ((L : ℝ) ^ d : ℂ) = ((L : ℝ) ^ d : ℂ) := by
    rw [show ((L : ℝ) ^ d : ℂ) = ((L : ℂ)) ^ d from by push_cast; ring, star_pow,
      Complex.star_def, Complex.conj_natCast]
  rw [div_eq_mul_inv, star_mul', star_inv₀, hden, ← div_eq_mul_inv]

/-- **Conjugate closeness**: if `ρ` is within `δ` of a real target `a`, so is `conj ρ`. -/
private theorem becStar_close (ρ : ℂ) (a δ : ℝ) (h : ‖ρ - (a : ℂ)‖ ≤ δ) :
    ‖star ρ - (a : ℂ)‖ ≤ δ := by
  have he : star ρ - (a : ℂ) = star (ρ - (a : ℂ)) := by
    rw [star_sub, Complex.star_def, Complex.conj_ofReal]
  rw [he, norm_star]; exact h

/-- **Diagonal second-moment concentration** (Tasaki §5.3, eq. (5.3.8)): for a realizing BEC
coherent family the coherent expectation `⟨Ξ_θ, Ô⁻Ô⁺ Ξ_θ⟩ / (L^d)²` converges to `m∗²`.  The
diagonal band `⟨Γ_M, Ô⁻Ô⁺ Γ_M⟩` equals `‖ρ_M‖²` on the raising side (`M ≥ 0`, `becLR_band_clean`)
and, via the exact commutator `Ô⁺Ô⁻ − Ô⁻Ô⁺ = 2 Ŝ³` (`becLR_eq_RL_sub_two`, `becRL_band_clean`),
equals `‖ρ_{M-1}‖² − 2M` on the lowering side (`M ≤ −1`); the `−2M/(L^d)²` residual is uniformly
small in the slow window (`M_win ≤ C₁ L^{d/2}`, `L^{d/2} ≤ L^d`), and each `‖ρ‖²` tends to `m∗²`. -/
theorem becLR_moment_limit (d : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ) (hC₁ : 0 < C₁) (θ : ℝ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ) (Mwin : ℕ → ℕ)
    (hFam : IsRealizingBECCoherentFamily d q₀ mStar C₁ Φ E₀ Mwin) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      ‖(star (becCoherentState d L θ (Mwin L) (Φ L)) ⬝ᵥ
          (staggeredLoweringOpS (torusParitySublattice d L) 1
            * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
            (becCoherentState d L θ (Mwin L) (Φ L)))
          / ((L : ℝ) ^ d : ℂ) ^ 2 - (mStar : ℂ) ^ 2‖ < ε := by
  intro ε hε
  obtain ⟨L₂, hsec⟩ := becRealizing_eventually_sector d q₀ mStar C₁ Φ E₀ Mwin hFam
  obtain ⟨Lsw, hLsw⟩ := Filter.eventually_atTop.mp hFam.1.2.2
  have hmStar : 0 < mStar := hFam.2.2.2
  set I : ℕ → Finset ℤ := fun L => Finset.Icc (-(Mwin L : ℤ)) (Mwin L : ℤ) with hI
  set bad : ℕ → Finset ℤ := fun L => {(-(Mwin L : ℤ)), (Mwin L : ℤ)} with hbad
  set v : ℕ → ℤ → ℂ := fun L M =>
    if h : 2 ≤ L ∧ Even L then
      letI : NeZero L := ⟨by have := h.1; omega⟩
      (star (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))) ⬝ᵥ
        (staggeredLoweringOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
        / ((L : ℝ) ^ d : ℂ) ^ 2
    else (mStar : ℂ) ^ 2 with hv
  have hbadsub : ∀ L, (2 ≤ L ∧ Even L) → bad L ⊆ I L := by
    intro L _ x hx
    rw [hbad, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [hI, Finset.mem_Icc]; rcases hx with h | h <;> omega
  have hbadcard : ∀ L, (2 ≤ L ∧ Even L) → (bad L).card ≤ 2 := by
    intro L _; rw [hbad]; exact le_trans (Finset.card_insert_le _ _) (by simp)
  have hcnt : ∀ L, (2 ≤ L ∧ Even L) →
      |((I L).card : ℝ) - (2 * (Mwin L : ℝ) + 1)| ≤ ((2 : ℕ) : ℝ) := by
    intro L _
    have hcard : (I L).card = 2 * Mwin L + 1 := by rw [hI, Int.card_Icc]; omega
    rw [hcard]; push_cast
    rw [show (2 * (Mwin L : ℝ) + 1) - (2 * (Mwin L : ℝ) + 1) = 0 from by ring, abs_zero]
    positivity
  have hBnn : (0 : ℝ) ≤ 1 + mStar ^ 2 := by positivity
  have hbdd : ∀ L, (2 ≤ L ∧ Even L) → ∀ M ∈ I L,
      ‖v L M - (mStar : ℂ) ^ 2‖ ≤ 1 + mStar ^ 2 := by
    intro L hgood M _
    haveI : NeZero L := ⟨by have := hgood.1; omega⟩
    have hvnorm : ‖v L M‖ ≤ 1 := by
      rw [hv]; simp only [dif_pos hgood]
      by_cases hz : towerState (torusParitySublattice d L) 1 M (Φ L) = 0
      · have hnum0 : (star (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))) ⬝ᵥ
            (staggeredLoweringOpS (torusParitySublattice d L) 1
              * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L)))) = 0 := by
          simp [hz, unitNormalize]
        rw [hnum0, zero_div, norm_zero]; norm_num
      · have hden : ‖((L : ℝ) ^ d : ℂ) ^ 2‖ = ((L : ℝ) ^ d) ^ 2 := by
          rw [norm_pow, show ((L : ℝ) ^ d : ℂ) = ((L : ℂ)) ^ d from by push_cast; ring, norm_pow,
            Complex.norm_natCast]
        have hnum := becTwoStepBand_norm_le d L hz hz
          (staggeredLoweringOpS (torusParitySublattice d L) 1
            * staggeredRaisingOpS (torusParitySublattice d L) 1)
          (becProductOp_norm_le d L _ _ (staggeredLoweringOpS_torus_norm_le d L)
            (staggeredRaisingOpS_torus_norm_le d L))
        have hLd0 : (0 : ℝ) < ((L : ℝ) ^ d) ^ 2 := by
          have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
          positivity
        rw [norm_div, hden, div_le_one hLd0]
        exact hnum
    have h2m : ‖(mStar : ℂ) ^ 2‖ = mStar ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
    calc ‖v L M - (mStar : ℂ) ^ 2‖ ≤ ‖v L M‖ + ‖(mStar : ℂ) ^ 2‖ := norm_sub_le _ _
      _ ≤ 1 + mStar ^ 2 := by rw [h2m]; linarith
  have hpin : ∀ ε' : ℝ, 0 < ε' → ∃ L₀ : ℕ, ∀ L : ℕ, (2 ≤ L ∧ Even L) → L₀ ≤ L →
      ∀ M ∈ I L, M ∉ bad L → ‖v L M - (mStar : ℂ) ^ 2‖ < ε' := by
    intro ε' hε'
    obtain ⟨Lp, hp⟩ := hFam.2.2.1 (ε' / (4 * (1 + mStar))) (by positivity)
    obtain ⟨Lres, hLres⟩ := exists_nat_gt (8 * C₁ / ε')
    refine ⟨max (max L₂ Lp) (max Lsw Lres), fun L hgood hL M hMI hMbad => ?_⟩
    haveI : NeZero L := ⟨by have := hgood.1; omega⟩
    obtain ⟨hsingL, hneL⟩ := hsec L (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hL))
      hgood.1 hgood.2
    have hLp : Lp ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hL)
    rw [hbad, Finset.mem_insert, Finset.mem_singleton, not_or] at hMbad
    rw [hI, Finset.mem_Icc] at hMI
    have hLdC : ((L : ℝ) ^ d : ℂ) ≠ 0 := by
      have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      have hpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
      exact_mod_cast hpos.ne'
    have hδ : (1 + mStar) * (ε' / (4 * (1 + mStar))) = ε' / 4 := by
      rw [mul_div_assoc']; field_simp
    rw [hv]; simp only [dif_pos hgood]
    by_cases hM0 : (0 : ℤ) ≤ M
    · -- raising side: band `= ρ · conj ρ`, `ρ = ⟨Γ_{M+1}, Ô⁺ Γ_M⟩ / L^d`
      have ht0 := hneL M (by omega) (by omega)
      have ht1 := hneL (M + 1) (by omega) (by omega)
      have hpM := hp L hLp hgood.1 hgood.2 M (by omega) (by omega)
      set ρ : ℂ := (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) (Φ L)))
          ⬝ᵥ (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
            (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
          / ((L : ℝ) ^ d : ℂ) with hρ
      have hxle : ‖ρ‖ ≤ 1 := becRatio_norm_le_one d L ht0 ht1
      have hveq : (star (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))) ⬝ᵥ
            (staggeredLoweringOpS (torusParitySublattice d L) 1
              * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
            / ((L : ℝ) ^ d : ℂ) ^ 2 = ρ * star ρ := by
        rw [becLR_band_clean (torusParitySublattice d L) hM0 ht1, hρ, becStar_ratio _ L d]; ring
      rw [hveq, sq]
      refine lt_of_le_of_lt (becProd_close ρ (star ρ) mStar (ε' / (4 * (1 + mStar)))
        hpM.le (becStar_close ρ mStar _ hpM.le) hxle) ?_
      rw [abs_of_pos hmStar, hδ]; linarith
    · -- lowering side: band `= ρ · conj ρ − 2M`, `ρ = ⟨Γ_M, Ô⁺ Γ_{M-1}⟩ / L^d`, plus residual
      have ht0 := hneL M (by omega) (by omega)
      have htm1 := hneL (M - 1) (by omega) (by omega)
      have hpMm1 := hp L hLp hgood.1 hgood.2 (M - 1) (by omega) (by omega)
      rw [show ((M : ℤ) - 1 + 1) = M from by ring] at hpMm1
      set ρ : ℂ := (star (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L)))
          ⬝ᵥ (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
            (unitNormalize (towerState (torusParitySublattice d L) 1 (M - 1) (Φ L))))
          / ((L : ℝ) ^ d : ℂ) with hρ
      have hxle : ‖ρ‖ ≤ 1 := becRatio_norm_le_one d L htm1 ht0
      -- residual `‖2M / (L^d)²‖ ≤ ε'/4`
      have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
        have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L); exact_mod_cast this
      have hMle : ‖(2 : ℂ) * (M : ℂ)‖ ≤ 2 * (Mwin L : ℝ) := by
        rw [norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num, Complex.norm_intCast]
        have hb : |(M : ℝ)| ≤ (Mwin L : ℝ) := by
          rw [abs_le]; constructor
          · exact_mod_cast (by omega : -(Mwin L : ℤ) ≤ M)
          · exact_mod_cast hMI.2
        linarith
      have hsw : (Mwin L : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) :=
        hLsw L (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hL))
      have hhalf : (L : ℝ) ^ ((d : ℝ) / 2) ≤ (L : ℝ) ^ d := by
        rw [← Real.rpow_natCast (L : ℝ) d]
        exact Real.rpow_le_rpow_of_exponent_le hL1
          (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
      have hLdge : (L : ℝ) ≤ (L : ℝ) ^ d := by
        calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (L : ℝ) ^ d := pow_le_pow_right₀ hL1 hd
      have hLdpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
      have hres : ‖(2 : ℂ) * (M : ℂ) / ((L : ℝ) ^ d : ℂ) ^ 2‖ ≤ ε' / 4 := by
        have hnormd : ‖((L : ℝ) ^ d : ℂ) ^ 2‖ = ((L : ℝ) ^ d) ^ 2 := by
          rw [norm_pow, show ((L : ℝ) ^ d : ℂ) = ((L : ℂ)) ^ d from by push_cast; ring, norm_pow,
            Complex.norm_natCast]
        rw [norm_div, hnormd]
        have hchain : ‖(2 : ℂ) * (M : ℂ)‖ ≤ 2 * C₁ * (L : ℝ) ^ d := by
          have h2 := mul_le_mul_of_nonneg_left hhalf hC₁.le
          calc ‖(2 : ℂ) * (M : ℂ)‖ ≤ 2 * (Mwin L : ℝ) := hMle
            _ ≤ 2 * (C₁ * (L : ℝ) ^ ((d : ℝ) / 2)) := by linarith [hsw]
            _ ≤ 2 * (C₁ * (L : ℝ) ^ d) := by linarith [h2]
            _ = 2 * C₁ * (L : ℝ) ^ d := by ring
        have hstep : ‖(2 : ℂ) * (M : ℂ)‖ / ((L : ℝ) ^ d) ^ 2 ≤ 2 * C₁ / (L : ℝ) := by
          rw [div_le_div_iff₀ (by positivity) (by linarith [hL1])]
          nlinarith [mul_le_mul hchain hLdge (by linarith [hL1] : (0 : ℝ) ≤ (L : ℝ))
            (by positivity : (0 : ℝ) ≤ 2 * C₁ * (L : ℝ) ^ d), hLdpos, hC₁.le]
        refine le_trans hstep ?_
        rw [div_le_div_iff₀ (by linarith [hL1]) (by norm_num)]
        have hLresL : Lres ≤ L :=
          le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hL)
        have hLgt : 8 * C₁ / ε' < (L : ℝ) := lt_of_lt_of_le hLres (by exact_mod_cast hLresL)
        rw [div_lt_iff₀ hε'] at hLgt; nlinarith [hLgt, hε', hL1]
      -- assemble: `v = ρ · conj ρ − 2M/(L^d)²`
      have hveq : (star (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))) ⬝ᵥ
            (staggeredLoweringOpS (torusParitySublattice d L) 1
              * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
            / ((L : ℝ) ^ d : ℂ) ^ 2 = ρ * star ρ - (2 : ℂ) * (M : ℂ) / ((L : ℝ) ^ d : ℂ) ^ 2 := by
        rw [becLR_eq_RL_sub_two (torusParitySublattice d L) M hsingL ht0,
          becRL_band_clean (torusParitySublattice d L) (by omega) htm1, sub_div]
        congr 1
        rw [hρ, becStar_ratio _ L d]; ring
      rw [hveq, show ρ * star ρ - (2 : ℂ) * (M : ℂ) / ((L : ℝ) ^ d : ℂ) ^ 2 - (mStar : ℂ) ^ 2
          = (ρ * star ρ - (mStar : ℂ) ^ 2) - (2 : ℂ) * (M : ℂ) / ((L : ℝ) ^ d : ℂ) ^ 2 from by ring]
      refine lt_of_le_of_lt (norm_sub_le _ _) ?_
      have hprod : ‖ρ * star ρ - (mStar : ℂ) ^ 2‖ ≤ ε' / 4 := by
        rw [sq]
        refine le_trans (becProd_close ρ (star ρ) mStar (ε' / (4 * (1 + mStar)))
          hpMm1.le (becStar_close ρ mStar _ hpMm1.le) hxle) ?_
        rw [abs_of_pos hmStar, hδ]
      linarith [hprod, hres]
  obtain ⟨L₀, hL₀⟩ := becWindowAvg_of_termwise Mwin
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hFam.1.2.1)
    ((mStar : ℂ) ^ 2) (1 + mStar ^ 2) hBnn 2 (fun L => 2 ≤ L ∧ Even L) v I bad
    hbadsub hbadcard hcnt hbdd hpin ε hε
  refine ⟨max L₀ L₂, fun L _ hL h2 hev => ?_⟩
  have hgood : 2 ≤ L ∧ Even L := ⟨h2, hev⟩
  obtain ⟨hsingL, _⟩ := hsec L (le_trans (le_max_right _ _) hL) h2 hev
  have hkey := hL₀ L hgood (le_trans (le_max_left _ _) hL)
  have hSum : ∑ M ∈ I L, v L M
      = (∑ M ∈ Finset.Icc (-(Mwin L : ℤ)) (Mwin L : ℤ),
          star (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))) ⬝ᵥ
            (staggeredLoweringOpS (torusParitySublattice d L) 1
              * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (unitNormalize (towerState (torusParitySublattice d L) 1 M (Φ L))))
        / ((L : ℝ) ^ d : ℂ) ^ 2 := by
    rw [Finset.sum_div, hI]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [hv]; simp only [dif_pos hgood]
  have hbridge : (star (becCoherentState d L θ (Mwin L) (Φ L)) ⬝ᵥ
        (staggeredLoweringOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ (Mwin L) (Φ L)))
        / ((L : ℝ) ^ d : ℂ) ^ 2
      = ((2 * (Mwin L : ℝ) + 1 : ℝ) : ℂ)⁻¹ * ∑ M ∈ I L, v L M := by
    rw [becCoherent_loweringRaising_collapse d L θ (Mwin L) (Φ L) hsingL, hSum]
    ring
  rw [hbridge]
  exact hkey

/-! ### Exact band identities between the diagonal and off-diagonal moments -/

/-- **Symmetric integer window sum vanishes**: `∑_{M=−a}^{a} M = 0` (the reflection `M ↦ −M`). -/
private theorem becSum_intCast_Icc_symm (a : ℤ) :
    ∑ M ∈ Finset.Icc (-a) a, (M : ℂ) = 0 := by
  have himg : (Finset.Icc (-a) a).map ⟨Neg.neg, neg_injective⟩ = Finset.Icc (-a) a := by
    ext x
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩; omega
    · intro hx; exact ⟨-x, by omega, by ring⟩
  have hmap := Finset.sum_map (Finset.Icc (-a) a) ⟨Neg.neg, neg_injective⟩ (fun M => (M : ℂ))
  rw [himg] at hmap
  simp only [Function.Embedding.coeFn_mk, Int.cast_neg] at hmap
  rw [Finset.sum_neg_distrib] at hmap
  linear_combination (2⁻¹ : ℂ) * hmap

/-- **Vanishing total-`Ŝ³` moment of the coherent state** (Tasaki §5.3): at half filling with the
tower states nonzero across the window, `⟨Ξ_θ, Ŝ³_tot Ξ_θ⟩ = 0`, because the diagonal band collapses
to the symmetric window sum `∑_M M = 0`. -/
theorem becCoherent_totalSpin3_expectation_zero (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0)
    (hne : ∀ M : ℤ, -(Mmax : ℤ) ≤ M → M ≤ (Mmax : ℤ) →
        towerState (torusParitySublattice d L) 1 M Φ ≠ 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
      (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec (becCoherentState d L θ Mmax Φ) = 0 := by
  have horth : ∀ M M' : ℤ, M' ≠ M →
      star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
        (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec
          (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) = 0 := by
    intro M M' hMM'
    rw [towerState_uN_totalSpin3_eigenvector (torusParitySublattice d L) M hsing, dotProduct_smul,
      smul_eq_mul, towerState_unitNormalize_inner_eq_zero_of_ne (torusParitySublattice d L)
        hMM'.symm hsing, mul_zero]
  rw [becCoherent_diagonal_collapse d L θ Mmax Φ _ horth]
  have hdiag : ∀ M ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
      star (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) ⬝ᵥ
        (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec
          (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) = (M : ℂ) := by
    intro M hM
    rw [Finset.mem_Icc] at hM
    have hpos : 0 < vecNormSqRe (towerState (torusParitySublattice d L) 1 M Φ) := by
      rw [vecNormSqRe]
      exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr (hne M hM.1 hM.2))).1
    rw [towerState_uN_totalSpin3_eigenvector (torusParitySublattice d L) M hsing, dotProduct_smul,
      smul_eq_mul, unitNormalize_dotProduct_self _ hpos, mul_one]
  rw [Finset.sum_congr rfl hdiag, becSum_intCast_Icc_symm, mul_zero]

/-- **Diagonal band equality** (Tasaki §5.3, eq. (4.2.32)): at half filling with nonvanishing tower
states, `⟨Ξ_θ, Ô⁺Ô⁻ Ξ_θ⟩ = ⟨Ξ_θ, Ô⁻Ô⁺ Ξ_θ⟩`, since their difference is `⟨Ξ_θ, 2 Ŝ³ Ξ_θ⟩ = 0`. -/
theorem becCoherent_RL_eq_LR (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0)
    (hne : ∀ M : ℤ, -(Mmax : ℤ) ≤ M → M ≤ (Mmax : ℤ) →
        towerState (torusParitySublattice d L) 1 M Φ ≠ 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1
          * staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)
      = star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredLoweringOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ) := by
  have hcomm := staggeredOrder_commutator (torusParitySublattice d L) (N := 1)
  have hz := becCoherent_totalSpin3_expectation_zero d L θ Mmax Φ hsing hne
  have hsub : star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1
          * staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)
      - star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredLoweringOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ) = 0 := by
    rw [← dotProduct_sub, ← Matrix.sub_mulVec, hcomm, Matrix.smul_mulVec, dotProduct_smul, hz,
      smul_zero]
  exact sub_eq_zero.mp hsub

/-- **Lowering–lowering is the conjugate raising–raising moment** (Tasaki §5.3, eq. (5.3.8)):
`⟨Ξ_θ, Ô⁻Ô⁻ Ξ_θ⟩ = conj ⟨Ξ_θ, Ô⁺Ô⁺ Ξ_θ⟩`, since `(Ô⁺Ô⁺)ᴴ = Ô⁻Ô⁻`. -/
theorem becCoherent_LL_eq_conj_RR (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredLoweringOpS (torusParitySublattice d L) 1
          * staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)
      = star (star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)) := by
  have hHH : staggeredLoweringOpS (torusParitySublattice d L) 1
        * staggeredLoweringOpS (torusParitySublattice d L) 1
      = Matrix.conjTranspose (staggeredRaisingOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1) := by
    rw [Matrix.conjTranspose_mul, staggeredRaisingOpS_conjTranspose]
  have hR : star (star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ))
      = star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (Matrix.conjTranspose (staggeredRaisingOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1)).mulVec
          (becCoherentState d L θ Mmax Φ) := by
    rw [Matrix.star_dotProduct, star_star, star_mulVec_dotProduct]
  rw [hHH, ← hR]

end LatticeSystem.Quantum
