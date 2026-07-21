import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSqConcentration
import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSqCollapse

/-!
# Tasaki §4.2.2 Proposition 4.10 (L5-b-iii): geometrisation of the `ô²`-moment collapse

The geometric moment step of the `ô²`-moment collapse driving Proposition 4.10.  With the
`ô²`-moments `R_k := orderSqMoment d L N Φ k = ⟨Φ, (ô²)^k Φ⟩`, `V² := (L^d)²` and the
`V²`-normalised moment `T_n := R_n / (R_0 · V^{2n})`, this module turns the two one-sided ratio
inputs into the collapse of the moment ratio driving Tasaki eq. (4.2.60):

* **`orderSqMoment_geom_lower`** — the concentration-**independent** lower bound
  `s_0^n ≤ T_n` (`s_0 = R_1 / (R_0 · V²)`), obtained by iterating log-convexity
  (`orderSqMoment_sq_le`) from the exact base ratio through `real_logConvex_geometric_lower`;
* **`orderSq_collapse_ratio_tendsto_one`** — the collapse tip: for each fixed `j`,
  `R_j / (√R_{2j} · √R_0) → 1` (the RHS of the L5-a identity `orderSq_collapse_vecNormSqRe`
  `= 2 (1 − R_j / (√R_{2j} √R_0))` therefore tends to `0`).  This is scale invariance:
  `R_j / (√R_{2j} √R_0) = T_j / √T_{2j} → (m∗)^{2j} / √((m∗)^{4j}) = 1` (`m∗ > 0`).

Everything is conditional on Conjecture 4.12 (`hconj`, `m∗ = √(3 q∗)`, never asserted true) and on
long-range order (vacuous in one dimension by Corollary 4.3), matching the hypothesis surface of the
base ratio and concentration inputs.  The assembly of this collapse into the sphere-average constant
predicate (via Tasaki Lemma 4.16, the diagonal extraction) is the sequel arc PR-6.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Proposition 4.10, eqs. (4.2.37), (4.2.57)–(4.2.61), pp. 105–108.
-/

namespace LatticeSystem.Quantum

open Matrix Filter Topology
open scoped ComplexOrder

/-! ### The concentration-independent geometric lower bound -/

/-- **Geometric lower bound for the normalised `ô²`-moment** (Prop 4.10, L5-b-iii, eq. (4.2.37)):
for `Φ ≠ 0` (`0 < R_0`), the `V²`-normalised moment dominates the `n`-th power of the base ratio
`s_0 = R_1 / (R_0 · V²)`:

`(R_1 / (R_0 · V²))^n ≤ R_n / (R_0 · V^{2n})`,

where `R_k = orderSqMoment d L N Φ k` and `V² = (L^d)²`.  This is concentration-independent: it is
the log-convexity (`orderSqMoment_sq_le`) telescoped from the *exact* base ratio `R_1 / R_0` through
`real_logConvex_geometric_lower`, giving `(R_1 / R_0)^n · R_0 ≤ R_n`, then normalised by
`R_0 · V^{2n} > 0`. -/
theorem orderSqMoment_geom_lower (d L N : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hR0 : 0 < orderSqMoment d L N Φ 0) (n : ℕ) :
    (orderSqMoment d L N Φ 1 / (orderSqMoment d L N Φ 0 * ((L : ℝ) ^ d) ^ 2)) ^ n
      ≤ orderSqMoment d L N Φ n
          / (orderSqMoment d L N Φ 0 * (((L : ℝ) ^ d) ^ 2) ^ n) := by
  set R := orderSqMoment d L N Φ with hRdef
  set V2 := ((L : ℝ) ^ d) ^ 2 with hV2def
  have hV2pos : 0 < V2 := by
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  -- Telescoped lower bound from the exact base ratio `R_1 / R_0`.
  have hkey : ∀ m : ℕ, (R 1 / R 0) ^ m * R 0 ≤ R m := by
    intro m
    cases m with
    | zero => simp
    | succ k =>
      exact LatticeSystem.Math.real_logConvex_geometric_lower (orderSqMoment_nonneg d L N Φ)
        (orderSqMoment_sq_le d L N Φ) (div_nonneg (orderSqMoment_nonneg d L N Φ 1) hR0.le)
        hR0 (le_of_eq (div_mul_cancel₀ (R 1) hR0.ne')) k
  -- Normalise by `R_0 · V^{2n} > 0`.
  rw [← div_div, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (R 1 / R 0) ^ n * (R 0 * V2 ^ n)
        = (R 1 / R 0) ^ n * R 0 * V2 ^ n := by ring
    _ ≤ R n * V2 ^ n := mul_le_mul_of_nonneg_right (hkey n) (by positivity)

/-! ### Filter plumbing for the even-`L` limits -/

/-- The filter `atTop ⊓ 𝓟 {L | Even L}` capturing "eventually along even `L`", the mode of
convergence of the `ô²`-moment ratios (matching the even-`L` `ε`–`δ` layers of the base ratio and
concentration inputs). -/
private def evenAtTop : Filter ℕ := Filter.atTop ⊓ Filter.principal {L : ℕ | Even L}

/-- Unfolding of the even-`L` eventually filter to an explicit threshold statement. -/
private theorem eventually_evenAtTop {p : ℕ → Prop} :
    (∀ᶠ L in evenAtTop, p L) ↔ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → Even L → p L := by
  simp only [evenAtTop, eventually_inf_principal, Set.mem_setOf_eq, eventually_atTop, ge_iff_le]

/-- The totalised `V²`-normalised `ô²`-moment `T_n L := R_n / (R_0 · V^{2n})` (junk value `0` at
`L = 0`), a total function `ℕ → ℝ` in `L` so that its even-`L` limit can be phrased with
`Filter.Tendsto`. -/
private noncomputable def normOrderSqMoment (d N : ℕ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (n L : ℕ) : ℝ :=
  if h : L = 0 then 0
  else @orderSqMoment d L N ⟨h⟩ (Φ L) n
    / (@orderSqMoment d L N ⟨h⟩ (Φ L) 0 * (((L : ℝ) ^ d) ^ 2) ^ n)

/-- Evaluation of `normOrderSqMoment` at a nonzero `L`: it is the genuine `V²`-normalised moment. -/
private theorem normOrderSqMoment_eq (d N : ℕ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (n L : ℕ) [NeZero L] :
    normOrderSqMoment d N Φ n L
      = orderSqMoment d L N (Φ L) n
          / (orderSqMoment d L N (Φ L) 0 * (((L : ℝ) ^ d) ^ 2) ^ n) := by
  rw [normOrderSqMoment, dif_neg (NeZero.ne L)]

/-- The totalised collapse ratio `R_j / (√R_{2j} · √R_0)` (junk value `0` at `L = 0`), a total
function `ℕ → ℝ` in `L` so that its even-`L` limit can be phrased with `Filter.Tendsto`. -/
private noncomputable def collapseRatioTot (d N : ℕ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (j L : ℕ) : ℝ :=
  if h : L = 0 then 0
  else @orderSqMoment d L N ⟨h⟩ (Φ L) j
    / (Real.sqrt (@orderSqMoment d L N ⟨h⟩ (Φ L) (2 * j)) *
        Real.sqrt (@orderSqMoment d L N ⟨h⟩ (Φ L) 0))

/-- Evaluation of `collapseRatioTot` at a nonzero `L`: it is the genuine collapse ratio. -/
private theorem collapseRatioTot_eq (d N : ℕ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (j L : ℕ) [NeZero L] :
    collapseRatioTot d N Φ j L
      = orderSqMoment d L N (Φ L) j
          / (Real.sqrt (orderSqMoment d L N (Φ L) (2 * j)) *
              Real.sqrt (orderSqMoment d L N (Φ L) 0)) := by
  rw [collapseRatioTot, dif_neg (NeZero.ne L)]

/-! ### The fixed-`n` geometric moment limit -/

/-- **Filter form of the geometric moment limit**: `T_n → (m∗)^{2n}` along even `L`.  The squeeze
combines the log-convex lower bound `s_0^n ≤ T_n` (`orderSqMoment_geom_lower`) driven to `(m∗)^{2n}`
by the base ratio limit, and the concentration upper bound telescoped through `T_{n+1} = s_n · T_n`
(`orderSqMoment_ratio_le_mStarSq`). -/
private theorem geom_tendsto_filter (d N : ℕ) (hd : 1 ≤ d)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsinglet : ∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
      (totalSpinSOp3 (HypercubicTorus d L) N).mulVec (Φ L) = 0 ∧
        (totalSpinSOp1 (HypercubicTorus d L) N).mulVec (Φ L) = 0)
    (qStar mStar : ℝ)
    (hlim3 : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      |(star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
          staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
          ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2) - qStar| < ε)
    (hconj : IsConjecture412Equality mStar qStar)
    (hR : ∃ Lr : ℕ, ∀ (n L : ℕ) [NeZero L], Lr ≤ L → 2 ≤ L → Even L →
      0 < orderSqMoment d L N (Φ L) n) (n : ℕ) :
    Tendsto (fun L => normOrderSqMoment d N Φ n L) evenAtTop (𝓝 ((mStar ^ 2) ^ n)) := by
  obtain ⟨Lr, hRpt⟩ := hR
  -- "Good" `L`: even, `≥ 2` (hence `NeZero`) and past the moment-positivity threshold `Lr`.
  have hgood : ∀ᶠ L in evenAtTop, 2 ≤ L ∧ Even L ∧ Lr ≤ L := by
    rw [eventually_evenAtTop]
    exact ⟨max 2 Lr, fun L hL hev => ⟨by omega, hev, by omega⟩⟩
  -- Base ratio limit as a filter statement: `s_0 = T_1 → (m∗)²`.
  have hbaseF : Tendsto (fun L => normOrderSqMoment d N Φ 1 L) evenAtTop (𝓝 (mStar ^ 2)) := by
    rw [Metric.tendsto_nhds]; intro ε hε
    rw [eventually_evenAtTop]
    obtain ⟨L₀, hL₀⟩ :=
      orderSqMoment_baseRatio_tendsto d N Φ hsinglet qStar mStar hlim3 hconj ε hε
    refine ⟨max L₀ 2, fun L hL hev => ?_⟩
    haveI : NeZero L := ⟨by omega⟩
    rw [normOrderSqMoment_eq, pow_one, Real.dist_eq]
    exact hL₀ L (le_trans (le_max_left _ _) hL) (by omega) hev
  -- The log-convex lower bound `s_0^n ≤ T_n`, eventually.
  have hle : ∀ᶠ L in evenAtTop,
      (normOrderSqMoment d N Φ 1 L) ^ n ≤ normOrderSqMoment d N Φ n L := by
    filter_upwards [hgood] with L hgd
    obtain ⟨h2, hev, hLr⟩ := hgd
    haveI : NeZero L := ⟨by omega⟩
    rw [normOrderSqMoment_eq, normOrderSqMoment_eq, pow_one]
    exact orderSqMoment_geom_lower d L N (Φ L) (hRpt 0 L hLr h2 hev) n
  -- The concentration upper bound, telescoped through `T_{n+1} = s_n · T_n`.
  have hUpper : ∀ (m : ℕ) (ε' : ℝ), 0 < ε' →
      ∀ᶠ L in evenAtTop, normOrderSqMoment d N Φ m L ≤ (mStar ^ 2 + ε') ^ m := by
    intro m
    induction m with
    | zero =>
      intro ε' _
      filter_upwards [hgood] with L hgd
      obtain ⟨h2, hev, hLr⟩ := hgd
      haveI : NeZero L := ⟨by omega⟩
      rw [normOrderSqMoment_eq]
      simp only [pow_zero, mul_one]
      rw [div_self (hRpt 0 L hLr h2 hev).ne']
    | succ k ih =>
      intro ε' hε'
      have hupk := ih ε' hε'
      rw [eventually_evenAtTop] at hupk ⊢
      obtain ⟨L₁, hL₁⟩ := hupk
      obtain ⟨L₂, hL₂⟩ := orderSqMoment_ratio_le_mStarSq d N hd Φ hsinglet qStar mStar hlim3 hconj
        ⟨Lr, hRpt⟩ k ε' hε'
      refine ⟨max (max (max L₁ L₂) Lr) 2, fun L hL hev => ?_⟩
      have h2 : 2 ≤ L := le_trans (le_max_right _ _) hL
      have hLr : Lr ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
      haveI : NeZero L := ⟨by omega⟩
      have hTk : normOrderSqMoment d N Φ k L ≤ (mStar ^ 2 + ε') ^ k :=
        hL₁ L (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
          (le_max_left _ _)) hL) hev
      have hsk : orderSqMoment d L N (Φ L) (k + 1) /
          (orderSqMoment d L N (Φ L) k * ((L : ℝ) ^ d) ^ 2) < mStar ^ 2 + ε' :=
        hL₂ L (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
          (le_max_left _ _)) hL) h2 hev
      have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
      have hRk0 : orderSqMoment d L N (Φ L) k ≠ 0 := (hRpt k L hLr h2 hev).ne'
      have hR00 : orderSqMoment d L N (Φ L) 0 ≠ 0 := (hRpt 0 L hLr h2 hev).ne'
      have hV20 : ((L : ℝ) ^ d) ^ 2 ≠ 0 := by positivity
      have hrec : normOrderSqMoment d N Φ (k + 1) L
          = (orderSqMoment d L N (Φ L) (k + 1) /
              (orderSqMoment d L N (Φ L) k * ((L : ℝ) ^ d) ^ 2)) * normOrderSqMoment d N Φ k L := by
        rw [normOrderSqMoment_eq, normOrderSqMoment_eq]; field_simp; ring
      have hTk0 : 0 ≤ normOrderSqMoment d N Φ k L := by
        rw [normOrderSqMoment_eq]
        exact div_nonneg (orderSqMoment_nonneg d L N (Φ L) k)
          (mul_nonneg (orderSqMoment_nonneg d L N (Φ L) 0) (by positivity))
      rw [hrec]
      calc (orderSqMoment d L N (Φ L) (k + 1) /
              (orderSqMoment d L N (Φ L) k * ((L : ℝ) ^ d) ^ 2)) * normOrderSqMoment d N Φ k L
          ≤ (mStar ^ 2 + ε') * (mStar ^ 2 + ε') ^ k :=
            mul_le_mul hsk.le hTk hTk0 (by positivity)
        _ = (mStar ^ 2 + ε') ^ (k + 1) := (pow_succ' _ _).symm
  -- Continuity of `t ↦ (m∗² + t)^n` at `0`: shrink the upper slack `ε'` below `ε`.
  have hcont : ∀ ε : ℝ, 0 < ε → ∃ ε' : ℝ, 0 < ε' ∧ (mStar ^ 2 + ε') ^ n < (mStar ^ 2) ^ n + ε := by
    intro ε hε
    have hct : ContinuousAt (fun t : ℝ => (mStar ^ 2 + t) ^ n) 0 :=
      ((continuous_const.add continuous_id).pow n).continuousAt
    have hmem : Set.Iio ((mStar ^ 2) ^ n + ε) ∈ 𝓝 ((fun t : ℝ => (mStar ^ 2 + t) ^ n) 0) := by
      have h0 : (fun t : ℝ => (mStar ^ 2 + t) ^ n) 0 = (mStar ^ 2) ^ n := by simp
      rw [h0]; exact Iio_mem_nhds (by linarith)
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), (mStar ^ 2 + t) ^ n < (mStar ^ 2) ^ n + ε := hct hmem
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hδsub⟩ := hev
    refine ⟨δ / 2, by positivity, hδsub ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  -- The squeeze.
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨ε', hε', hcont'⟩ := hcont ε hε
  have hlowF := Metric.tendsto_nhds.mp (hbaseF.pow n) ε hε
  have hupF := hUpper n ε' hε'
  filter_upwards [hlowF, hupF, hle] with L hlow hup hlen
  rw [Real.dist_eq] at hlow ⊢
  rw [abs_lt] at hlow ⊢
  exact ⟨by linarith [hlow.1, hlen], by linarith [hup, hcont']⟩

/-! ### The collapse-ratio tip -/

/-- **Moment collapse ratio tends to one** (Prop 4.10, L5-b-iii tip, Tasaki eq. (4.2.60) RHS):
for a total-spin-singlet ground-state family `Φ` with long-range order, **conditional on
Conjecture 4.12** (`hconj`) and with `0 < m∗` (`hmStar`), for each fixed `j`

`∀ ε > 0, ∃ L₀, ∀ L ≥ L₀ (even, ≥ 2), |R_j / (√R_{2j} · √R_0) − 1| < ε`,

where `R_k = orderSqMoment d L N Φ k`.  Equivalently (with the L5-a identity
`orderSq_collapse_vecNormSqRe = 2 (1 − R_j / (√R_{2j} √R_0))`) the collapse distance
`‖unitNormalize ((ô²)ʲ Φ) − Φ̂‖²` tends to `0`.  Proof: scale invariance
`R_j / (√R_{2j} √R_0) = T_j / √T_{2j}` with `T_n = R_n / (R_0 · V^{2n})`, then
`T_j → (m∗)^{2j}`, `√T_{2j} → √((m∗)^{4j}) = (m∗)^{2j}` (`geom_tendsto_filter`), so the ratio
tends to `(m∗)^{2j} / (m∗)^{2j} = 1` (`m∗ > 0`). -/
theorem orderSq_collapse_ratio_tendsto_one (d N : ℕ) (hd : 1 ≤ d)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsinglet : ∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
      (totalSpinSOp3 (HypercubicTorus d L) N).mulVec (Φ L) = 0 ∧
        (totalSpinSOp1 (HypercubicTorus d L) N).mulVec (Φ L) = 0)
    (qStar mStar : ℝ) (hmStar : 0 < mStar)
    (hlim3 : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      |(star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
          staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
          ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2) - qStar| < ε)
    (hconj : IsConjecture412Equality mStar qStar)
    (hR : ∃ Lr : ℕ, ∀ (n L : ℕ) [NeZero L], Lr ≤ L → 2 ≤ L → Even L →
      0 < orderSqMoment d L N (Φ L) n) (j : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      |orderSqMoment d L N (Φ L) j /
          (Real.sqrt (orderSqMoment d L N (Φ L) (2 * j)) *
            Real.sqrt (orderSqMoment d L N (Φ L) 0)) - 1| < ε := by
  have hmStar2pos : 0 < mStar ^ 2 := pow_pos hmStar 2
  obtain ⟨Lr, hRpt⟩ := hR
  -- The two fixed-`n` limits, as filter statements.
  have hj := geom_tendsto_filter d N hd Φ hsinglet qStar mStar hlim3 hconj ⟨Lr, hRpt⟩ j
  have h2j := geom_tendsto_filter d N hd Φ hsinglet qStar mStar hlim3 hconj ⟨Lr, hRpt⟩ (2 * j)
  -- `√((m∗²)^{2j}) = (m∗²)^j`.
  have hden_lim : Real.sqrt ((mStar ^ 2) ^ (2 * j)) = (mStar ^ 2) ^ j := by
    rw [mul_comm 2 j, pow_mul, Real.sqrt_sq (by positivity)]
  -- The ratio of totalised moments tends to `1`.
  have hdiv : Tendsto (fun L => normOrderSqMoment d N Φ j L /
      Real.sqrt (normOrderSqMoment d N Φ (2 * j) L)) evenAtTop (𝓝 1) := by
    have hb := h2j.sqrt
    rw [hden_lim] at hb
    have := hj.div hb (pow_pos hmStar2pos j).ne'
    rwa [div_self (pow_pos hmStar2pos j).ne'] at this
  -- Scale invariance `R_j / (√R_{2j} √R_0) = T_j / √T_{2j}` for good `L`.
  have hgood : ∀ᶠ L in evenAtTop, 2 ≤ L ∧ Even L ∧ Lr ≤ L := by
    rw [eventually_evenAtTop]
    exact ⟨max 2 Lr, fun L hL hev => ⟨by omega, hev, by omega⟩⟩
  have hCollapseEq : ∀ᶠ L in evenAtTop,
      normOrderSqMoment d N Φ j L / Real.sqrt (normOrderSqMoment d N Φ (2 * j) L)
        = collapseRatioTot d N Φ j L := by
    filter_upwards [hgood] with L hgd
    obtain ⟨h2, hev, hLr⟩ := hgd
    haveI : NeZero L := ⟨by omega⟩
    rw [collapseRatioTot_eq]
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
    have hr0 := orderSqMoment_nonneg d L N (Φ L) 0
    have hr2j := orderSqMoment_nonneg d L N (Φ L) (2 * j)
    have hVpow : Real.sqrt ((((L : ℝ) ^ d) ^ 2) ^ (2 * j)) = (((L : ℝ) ^ d) ^ 2) ^ j := by
      rw [show 2 * j = j * 2 from by ring, pow_mul, Real.sqrt_sq (by positivity)]
    rw [normOrderSqMoment_eq, normOrderSqMoment_eq, Real.sqrt_div hr2j, Real.sqrt_mul hr0, hVpow]
    set a := Real.sqrt (orderSqMoment d L N (Φ L) 0) with ha_def
    set b := Real.sqrt (orderSqMoment d L N (Φ L) (2 * j)) with hb_def
    set v := (((L : ℝ) ^ d) ^ 2) ^ j with hv_def
    have haR0 : orderSqMoment d L N (Φ L) 0 = a * a := (Real.mul_self_sqrt hr0).symm
    have ha0 : a ≠ 0 := by rw [ha_def]; exact Real.sqrt_ne_zero'.mpr (hRpt 0 L hLr h2 hev)
    have hb0 : b ≠ 0 := by rw [hb_def]; exact Real.sqrt_ne_zero'.mpr (hRpt (2 * j) L hLr h2 hev)
    have hv0 : v ≠ 0 := by rw [hv_def]; positivity
    rw [haR0]
    field_simp
  -- Transport the limit through the pointwise identity, then read off `ε`–`δ`.
  have hFinal := hdiv.congr' hCollapseEq
  intro ε hε
  have hev := Metric.tendsto_nhds.mp hFinal ε hε
  rw [eventually_evenAtTop] at hev
  obtain ⟨L₀, hL₀⟩ := hev
  refine ⟨max L₀ 2, fun L _ hL h2 hev => ?_⟩
  have hd' := hL₀ L (le_trans (le_max_left _ _) hL) hev
  rwa [collapseRatioTot_eq, Real.dist_eq] at hd'

end LatticeSystem.Quantum
