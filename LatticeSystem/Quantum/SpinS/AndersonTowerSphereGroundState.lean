import LatticeSystem.Quantum.SpinS.AndersonTowerSphereDischargeParts
import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSqGeom
import LatticeSystem.Quantum.SpinS.AndersonTowerTheorem49
import LatticeSystem.Math.DoubleSequenceDiagonal

/-!
# Tasaki §4.2.2 Proposition 4.10: final discharge (the solid-angle average is the ground state)

Assembly of the sphere-average discharge (PR-6c-ii).  Assuming Conjecture 4.12 (`m∗ = √(3 q∗)`, kept
as an explicit hypothesis, never asserted) and the `ô²`-concentration documented axiom
(`orderSqMoment_ratio_le_mStarSq`), the normalized solid-angle average of the symmetry-breaking
states `|Ξ_n⟩` converges, up to a unimodular phase (here `z = 1`), to the ground state `|Φ_GS⟩` as
`L ↑ ∞` (eq. (4.2.22)).

The proof bundles the first three constant-family statements from Theorem 4.9
(`tanakaSSB_full_symmetry_breaking`) and, for the fourth (`IsTanakaSphereAverageConstants`),
assembles:

* a **per-volume triangle bound** (`sphereGS_triangle_bound`) splitting the normalized distance into
  the operator vs `(ô²)ʲ` remainder (`sphereAverage_op_unitNormalize_sub_le`, PR-6c-i) plus the
  `(ô²)ʲ` collapse distance (`orderSq_collapse_vecNormSqRe`, L5-a);
* the vanishing of the first term (`sphereAverage_rhsA_tendsto_zero`: the `Φ`-independent bound is
  `O(1/V)`);
* the vanishing of the second term via the collapse-ratio limit
  (`orderSq_collapse_ratio_tendsto_one`, L5-b-iii, conditional on Conjecture 4.12 and the
  `ô²`-concentration axiom);
* a **capped diagonal** (`diagonal_tendsto_zero_capped`) extracting a slowly diverging
  `M(L) = 2 m(L)` with `m(L) ≤ κ(L) = ⌊(C₁ L^{d/2} − 1)/2⌋₊`, giving both the growth bound
  `M L + 1 ≤ C₁ L^{d/2}` and the vanishing distance; the even reduction
  `unitNormalize(Ξ_avg) = unitNormalize(Op_{2m} Φ)`
  (`solidAngleAverageTanaka_unitNormalize_eq_orderPow`, 6a) closes the vector clause with `z = 1`.

In one dimension the long-range-order premise is unsatisfiable (Corollary 4.3), and for `N = 0` the
order operator vanishes, so both degenerate cases are vacuous.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1–4.2.2, Proposition 4.10, eqs. (4.2.17)–(4.2.22), (4.2.57)–(4.2.61), pp. 99–100,
108–109; Koma, Tasaki, J. Stat. Phys. **76** (1994) 745–803 [66].
-/

namespace LatticeSystem.Quantum

open Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Frobenius ComplexOrder

/-- **First term vanishes** (`O(1/V)`).  For fixed `j ≥ 1`, the `Φ`-independent per-volume bound of
`sphereAverage_op_unitNormalize_sub_le` — of order `V^{2j−1}/V^{2j} = V^{−1}` in the volume
`V = L^d` — tends to `0` as `L ↑ ∞`.  Proven by rewriting the bound as `K · (L^d)⁻¹` for `L ≥ 1`. -/
private theorem sphereAverage_rhsA_tendsto_zero (d N j : ℕ) (hd : 1 ≤ d) (hj : 1 ≤ j)
    {q₀ : ℝ} (hq₀ : 0 < q₀) :
    Tendsto (fun L : ℕ => 2 * cartPinchVecPoly j * ((L : ℝ) ^ d * N) ^ (2 * j - 1)
        / (4 * Real.pi / (2 * j + 1) * (q₀ * ((L : ℝ) ^ d) ^ 2) ^ j)) atTop (𝓝 0) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hpi := Real.pi_pos
  have hden : Tendsto (fun L : ℕ => (L : ℝ) ^ d) atTop atTop :=
    (tendsto_pow_atTop (by omega : d ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun L : ℕ => ((L : ℝ) ^ d)⁻¹) atTop (𝓝 0) := hden.inv_tendsto_atTop
  have hKlim : Tendsto (fun L : ℕ => (2 * cartPinchVecPoly (i + 1) * (N : ℝ) ^ (2 * (i + 1) - 1)
      / (4 * Real.pi / (2 * ((i : ℝ) + 1) + 1) * q₀ ^ (i + 1))) * ((L : ℝ) ^ d)⁻¹)
      atTop (𝓝 0) := by
    simpa using hinv.const_mul (2 * cartPinchVecPoly (i + 1) * (N : ℝ) ^ (2 * (i + 1) - 1)
      / (4 * Real.pi / (2 * ((i : ℝ) + 1) + 1) * q₀ ^ (i + 1)))
  refine hKlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with L hL1
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hqne : q₀ ≠ 0 := hq₀.ne'
  rw [show 2 * (i + 1) - 1 = 2 * i + 1 from by omega]
  generalize hVE : (L : ℝ) ^ d = V at hVpos ⊢
  have hV : V ≠ 0 := hVpos.ne'
  rw [mul_pow, mul_pow, ← pow_mul,
    show V ^ (2 * (i + 1)) = V ^ (2 * i + 1) * V from by
      rw [show 2 * (i + 1) = (2 * i + 1) + 1 from by omega, pow_succ]]
  push_cast
  field_simp

/-- **Per-volume triangle bound** (Prop 4.10 assembly core).  For `j ≥ 1` and a nonzero
long-range-ordered `Φ`, the normalized distance between the even sphere integral and the ground
state splits, in `L²` norm, into the operator vs `(ô²)ʲ` remainder
(`sphereAverage_op_unitNormalize_sub_le`) and the `(ô²)ʲ` collapse distance
(`orderSq_collapse_vecNormSqRe`):

`√(vecNormSqRe(unitNormalize(Op_{2j} Φ) − Φ̂))
  ≤ (Φ-independent O(1/V) bound) + √(2 (1 − R_j/(√R_{2j} √R_0)))`. -/
private theorem sphereGS_triangle_bound (d N j L : ℕ) [NeZero L] (hN : 1 ≤ N) (hj : 1 ≤ j)
    {q₀ : ℝ} (hq₀ : 0 < q₀) (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (hΦ : Φ ≠ 0)
    (hlro : q₀ ≤ (star Φ ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
        staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ)).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)) :
    Real.sqrt (vecNormSqRe (unitNormalize ((∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) (torusParitySublattice d L) N)
          ^ (2 * j) ∂volume.toSphere).mulVec Φ) - unitNormalize Φ))
      ≤ (2 * cartPinchVecPoly j * ((L : ℝ) ^ d * N) ^ (2 * j - 1)
          / (4 * Real.pi / (2 * j + 1) * (q₀ * ((L : ℝ) ^ d) ^ 2) ^ j))
        + Real.sqrt (2 * (1 - orderSqMoment d L N Φ j
            / (Real.sqrt (orderSqMoment d L N Φ (2 * j)) *
              Real.sqrt (orderSqMoment d L N Φ 0)))) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hR0pos : 0 < orderSqMoment d L N Φ 0 := by
    rw [show orderSqMoment d L N Φ 0 = (star Φ ⬝ᵥ Φ).re from by
      rw [orderSqMoment, pow_zero, Matrix.one_mulVec]]
    exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  have hpos2j : 0 < orderSqMoment d L N Φ (2 * j) :=
    lt_of_lt_of_le (mul_pos (pow_pos (mul_pos hq₀ (by positivity)) (2 * j)) hR0pos)
      (orderSqMoment_ge d L N Φ hΦ hq₀.le hlro (2 * j))
  refine le_trans (sqrt_vecNormSqRe_sub_triangle _
    (unitNormalize ((orderSqOp (torusParitySublattice d L) N ^ j).mulVec Φ)) _) ?_
  have hcollapse := orderSq_collapse_vecNormSqRe d L N j Φ hΦ hpos2j
  rw [hcollapse]
  gcongr
  exact sphereAverage_op_unitNormalize_sub_le d L N j hN hj hq₀ Φ hΦ hlro

/-- **Tasaki Proposition 4.10 (the solid-angle average is the ground state).**  Assuming
Conjecture 4.12 (`m∗ = √(3 q∗)`, an explicit hypothesis, never asserted true) and the
`ô²`-concentration documented axiom `orderSqMoment_ratio_le_mStarSq`, the normalized solid-angle
average of the symmetry-breaking states `|Ξ_n⟩` converges (up to a unimodular phase, here `z = 1`)
to the unique ground state `|Φ_GS⟩` as `L ↑ ∞` (eq. (4.2.22)): the `SU(2)`-symmetric average of the
symmetry-breaking "ground states" recovers the long-range-ordered but no-SSB ground state.

The theorem also asserts `IsTanakaFullSSBConstants d N q₀ C₁ mStar` (Theorem 4.9) alongside, so
`mStar` is the *same* full-SSB order parameter (`m∗ = √q₀`), letting downstream code combine
Proposition 4.10 with Theorem 4.9 for one physical order parameter.  Conditional on long-range order
(vacuous in one dimension by Corollary 4.3) and, for `N = 0`, vacuous since the order operator
vanishes.

`#print axioms` records `orderSqMoment_ratio_le_mStarSq` (the `ô²` concentration, deferred with
parity to the `p̂` mirror per the 2026-07-12 no-overreach boundary) alongside the standard three;
Conjecture 4.12 does not appear, being consumed only as a hypothesis.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Proposition 4.10, eqs. (4.2.22), (4.2.57)–(4.2.61), pp. 108–109. -/
theorem tanakaSphereAverage_groundState (d N : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ mStar : ℝ, IsAndersonTowerConstants d N q₀ C₁ C₂ ∧
      IsTanakaSSBConstants d N q₀ C₁ C₂ ∧
      IsTanakaFullSSBConstants d N q₀ C₁ mStar ∧
      IsTanakaSphereAverageConstants d N q₀ C₁ mStar := by
  obtain ⟨C₁, C₂, mStar, hAnd, hSSB, hFull⟩ := tanakaSSB_full_symmetry_breaking d N hd q₀ hq₀
  refine ⟨C₁, C₂, mStar, hAnd, hSSB, hFull, hFull.1, hFull.2.1, ?_⟩
  intro Φ E₀ hpremise qStar hlim3 hconj
  obtain ⟨L₁, hL₁⟩ := hpremise
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · -- `N = 0`: the order operator vanishes, so the long-range-order premise is unsatisfiable.
    exfalso
    subst hN0
    set L := 2 * (L₁ + 1) with hLdef
    haveI : NeZero L := ⟨by omega⟩
    obtain ⟨_, _, hΦ0, _, _, _, hlroΦ⟩ := hL₁ L (by omega) (by omega) ⟨L₁ + 1, by omega⟩
    have hO0 : staggeredOrderOpS (torusParitySublattice d L) 0 = 0 := by
      rw [staggeredOrderOpS]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      rw [spinSSiteOp3, show spinSOp3 0 = 0 from by
        ext a b; rw [spinSOp3, Matrix.diagonal_apply]
        rcases eq_or_ne a b with h | h
        · subst h; simp
        · simp [h], onSiteS_zero, smul_zero]
    have hm0c : 0 < (star (Φ L) ⬝ᵥ Φ L).re :=
      (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ0)).1
    rw [hO0] at hlroΦ
    simp only [zero_mul, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re, zero_div] at hlroΦ
    linarith [hlroΦ]
  · -- `N ≥ 1`: the capped-diagonal construction.
    have hC1 : 0 < C₁ := hFull.1
    have hmStar : 0 < mStar := hFull.2.1
    have hsinglet : ∃ Ls : ℕ, ∀ (L : ℕ) [NeZero L], Ls ≤ L → 2 ≤ L → Even L →
        (totalSpinSOp3 (HypercubicTorus d L) N).mulVec (Φ L) = 0 ∧
          (totalSpinSOp1 (HypercubicTorus d L) N).mulVec (Φ L) = 0 :=
      ⟨L₁, fun L _ hL h2 hev => by
        obtain ⟨_, _, _, hS3, hS1, _, _⟩ := hL₁ L hL h2 hev; exact ⟨hS3, hS1⟩⟩
    have hR : ∃ Lr : ℕ, ∀ (n L : ℕ) [NeZero L], Lr ≤ L → 2 ≤ L → Even L →
        0 < orderSqMoment d L N (Φ L) n := by
      refine ⟨L₁, fun n L _ hL h2 hev => ?_⟩
      obtain ⟨_, _, hΦ0, _, _, _, hlro⟩ := hL₁ L hL h2 hev
      have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
      have hR0pos : 0 < orderSqMoment d L N (Φ L) 0 := by
        rw [show orderSqMoment d L N (Φ L) 0 = (star (Φ L) ⬝ᵥ Φ L).re from by
          rw [orderSqMoment, pow_zero, Matrix.one_mulVec]]
        exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ0)).1
      exact lt_of_lt_of_le (mul_pos (pow_pos (mul_pos hq₀ (by positivity)) n) hR0pos)
        (orderSqMoment_ge d L N (Φ L) hΦ0 hq₀.le hlro n)
    -- The gated normalized distance sequence `f L j` (comparison state `z = 1`).
    set f : ℕ → ℕ → ℝ := fun L j =>
      if h : 1 ≤ j ∧ 2 ≤ L ∧ Even L ∧ L₁ ≤ L then
        letI : NeZero L := ⟨by have := h.2.1; omega⟩
        Real.sqrt (vecNormSqRe (unitNormalize
          ((∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
              (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) (torusParitySublattice d L) N)
                ^ (2 * j) ∂volume.toSphere).mulVec (Φ L)) - unitNormalize (Φ L)))
      else 0 with hfdef
    -- Per-`j` vanishing: `f L j → 0` as `L ↑ ∞`.
    have hg : ∀ j, Tendsto (fun L => f L j) atTop (𝓝 0) := by
      intro j
      rcases Nat.lt_or_ge j 1 with hj0 | hj
      · have hz : (fun L => f L j) = fun _ => (0 : ℝ) := by
          funext L; simp only [hfdef]; exact dif_neg (fun h => by have := h.1; omega)
        rw [hz]; exact tendsto_const_nhds
      · rw [Metric.tendsto_atTop]
        intro ε hε
        have hAlim := sphereAverage_rhsA_tendsto_zero d N j hd hj hq₀
        rw [Metric.tendsto_atTop] at hAlim
        obtain ⟨LA, hLA⟩ := hAlim (ε / 2) (by positivity)
        obtain ⟨LB, hLB⟩ := orderSq_collapse_ratio_tendsto_one d N hd Φ hsinglet qStar mStar
          hmStar hlim3 hconj hR j (ε ^ 2 / 8) (by positivity)
        refine ⟨max (max LA LB) (max L₁ 2), fun L hL => ?_⟩
        rw [Real.dist_eq, sub_zero]
        by_cases hgood : 2 ≤ L ∧ Even L ∧ L₁ ≤ L
        · obtain ⟨h2, hev, hLL1⟩ := hgood
          haveI : NeZero L := ⟨by omega⟩
          obtain ⟨_, _, hΦ0, _, _, _, hlro⟩ := hL₁ L hLL1 h2 hev
          have hgd4 : 1 ≤ j ∧ 2 ≤ L ∧ Even L ∧ L₁ ≤ L := ⟨hj, h2, hev, hLL1⟩
          have hfL : f L j = Real.sqrt (vecNormSqRe (unitNormalize
              ((∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
                  (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3))
                      (torusParitySublattice d L) N)
                    ^ (2 * j) ∂volume.toSphere).mulVec (Φ L)) - unitNormalize (Φ L))) := by
            simp only [hfdef, dif_pos hgd4]
          rw [hfL, abs_of_nonneg (Real.sqrt_nonneg _)]
          have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
          have hpos2j : 0 < orderSqMoment d L N (Φ L) (2 * j) := by
            have hR0pos : 0 < orderSqMoment d L N (Φ L) 0 := by
              rw [show orderSqMoment d L N (Φ L) 0 = (star (Φ L) ⬝ᵥ Φ L).re from by
                rw [orderSqMoment, pow_zero, Matrix.one_mulVec]]
              exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ0)).1
            exact lt_of_lt_of_le (mul_pos (pow_pos (mul_pos hq₀ (by positivity)) (2 * j)) hR0pos)
              (orderSqMoment_ge d L N (Φ L) hΦ0 hq₀.le hlro (2 * j))
          have hRHSA : 2 * cartPinchVecPoly j * ((L : ℝ) ^ d * N) ^ (2 * j - 1)
              / (4 * Real.pi / (2 * j + 1) * (q₀ * ((L : ℝ) ^ d) ^ 2) ^ j) < ε / 2 := by
            refine lt_of_le_of_lt (le_abs_self _) ?_
            have := hLA L (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL)
            rwa [Real.dist_eq, sub_zero] at this
          have hratio := hLB L (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL) h2 hev
          have hnn : (0 : ℝ) ≤ 2 * (1 - orderSqMoment d L N (Φ L) j
              / (Real.sqrt (orderSqMoment d L N (Φ L) (2 * j)) *
                Real.sqrt (orderSqMoment d L N (Φ L) 0))) := by
            rw [← orderSq_collapse_vecNormSqRe d L N j (Φ L) hΦ0 hpos2j, vecNormSqRe]
            exact (Complex.le_def.mp (dotProduct_star_self_nonneg _)).1
          have htermB : Real.sqrt (2 * (1 - orderSqMoment d L N (Φ L) j
              / (Real.sqrt (orderSqMoment d L N (Φ L) (2 * j)) *
                Real.sqrt (orderSqMoment d L N (Φ L) 0)))) ≤ ε / 2 := by
            have h1mr : 1 - orderSqMoment d L N (Φ L) j
                / (Real.sqrt (orderSqMoment d L N (Φ L) (2 * j)) *
                  Real.sqrt (orderSqMoment d L N (Φ L) 0)) < ε ^ 2 / 8 := by
              have := (abs_lt.mp hratio).1; linarith
            calc Real.sqrt (2 * (1 - _)) ≤ Real.sqrt (ε ^ 2 / 4) :=
                  Real.sqrt_le_sqrt (by linarith [h1mr])
              _ = ε / 2 := by
                  rw [show ε ^ 2 / 4 = (ε / 2) ^ 2 from by ring, Real.sqrt_sq (by positivity)]
          calc Real.sqrt (vecNormSqRe (unitNormalize (_) - unitNormalize (Φ L)))
              ≤ _ + Real.sqrt (2 * (1 - orderSqMoment d L N (Φ L) j
                  / (Real.sqrt (orderSqMoment d L N (Φ L) (2 * j)) *
                    Real.sqrt (orderSqMoment d L N (Φ L) 0)))) :=
                sphereGS_triangle_bound d N j L hN hj hq₀ (Φ L) hΦ0 hlro
            _ < ε / 2 + ε / 2 := by linarith [hRHSA, htermB]
            _ = ε := by ring
        · have hfL0 : f L j = 0 := by
            simp only [hfdef]; exact dif_neg (fun h => hgood ⟨h.2.1, h.2.2.1, h.2.2.2⟩)
          rw [hfL0, abs_zero]; exact hε
    -- The capped diagonal ceiling `κ L = ⌊(C₁ L^{d/2} − 1)/2⌋₊` diverges.
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hd2 : (0 : ℝ) < (d : ℝ) / 2 := by linarith
    have hrpow : Tendsto (fun L : ℕ => C₁ * (L : ℝ) ^ ((d : ℝ) / 2)) atTop atTop :=
      Tendsto.const_mul_atTop hC1 ((tendsto_rpow_atTop hd2).comp tendsto_natCast_atTop_atTop)
    have hcap : Tendsto (fun L : ℕ => (C₁ * (L : ℝ) ^ ((d : ℝ) / 2) - 1) / 2) atTop atTop := by
      have hsub : Tendsto (fun L : ℕ => C₁ * (L : ℝ) ^ ((d : ℝ) / 2) - 1) atTop atTop := by
        simpa using tendsto_atTop_add_const_right atTop (-1) hrpow
      exact hsub.atTop_div_const (by norm_num)
    set κ : ℕ → ℕ := fun L => ⌊(C₁ * (L : ℝ) ^ ((d : ℝ) / 2) - 1) / 2⌋₊ with hκdef
    have hκ : Tendsto κ atTop atTop := tendsto_nat_floor_atTop.comp hcap
    obtain ⟨m, hmtop, hmcap, hmlim⟩ :=
      LatticeSystem.Math.diagonal_tendsto_zero_capped f (fun _ => 0) κ hg tendsto_const_nhds hκ
    refine ⟨fun L => 2 * m L,
      tendsto_atTop_mono (fun L => Nat.le_mul_of_pos_left (m L) (by norm_num)) hmtop, ?_, ?_⟩
    · -- growth clause: `0 < M L ∧ M L + 1 ≤ C₁ L^{d/2}`.
      obtain ⟨L₂a, hL₂a⟩ := Filter.eventually_atTop.mp (hrpow.eventually_ge_atTop 1)
      obtain ⟨L₂b, hL₂b⟩ := tendsto_atTop_atTop.mp hmtop 1
      refine ⟨max L₂a L₂b, fun L _ hL _ _ => ?_⟩
      simp only []
      have hm1 : 1 ≤ m L := hL₂b L (le_trans (le_max_right _ _) hL)
      have hge1 : (1 : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) :=
        hL₂a L (le_trans (le_max_left _ _) hL)
      have harg : (0 : ℝ) ≤ (C₁ * (L : ℝ) ^ ((d : ℝ) / 2) - 1) / 2 := by linarith
      have hfloor : (κ L : ℝ) ≤ (C₁ * (L : ℝ) ^ ((d : ℝ) / 2) - 1) / 2 := by
        rw [hκdef]; exact Nat.floor_le harg
      have hmκ : (m L : ℝ) ≤ (κ L : ℝ) := by exact_mod_cast hmcap L
      refine ⟨by omega, ?_⟩
      have hcast : ((2 * m L : ℕ) : ℝ) + 1 = 2 * (m L : ℝ) + 1 := by push_cast; ring
      rw [hcast]; nlinarith [hfloor, hmκ]
    · -- vector clause: the normalized average converges to `Φ̂` (`z = 1`).
      intro ε hε
      rw [Metric.tendsto_atTop] at hmlim
      obtain ⟨L₀, hL₀⟩ := hmlim ε hε
      obtain ⟨L₀b, hL₀b⟩ := tendsto_atTop_atTop.mp hmtop 1
      refine ⟨max (max L₀ L₀b) (max L₁ 2), fun L _ hL h2 hev => ?_⟩
      simp only []
      have hLL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
      have hm1 : 1 ≤ m L := hL₀b L (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL)
      obtain ⟨_, _, hΦ0, hS3, hS1, _, _⟩ := hL₁ L hLL1 h2 hev
      refine ⟨1, norm_one, ?_⟩
      rw [one_smul]
      have h6a := solidAngleAverageTanaka_unitNormalize_eq_orderPow d L N (2 * m L) (Φ L) hS3 hS1
      rw [if_pos (even_two_mul (m L))] at h6a
      rw [h6a]
      have hfval : f L (m L) = Real.sqrt (vecNormSqRe (unitNormalize
          ((∫ n : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
              (directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) (torusParitySublattice d L) N)
                ^ (2 * m L) ∂volume.toSphere).mulVec (Φ L)) - unitNormalize (Φ L))) := by
        simp only [hfdef,
          dif_pos (show 1 ≤ m L ∧ 2 ≤ L ∧ Even L ∧ L₁ ≤ L from ⟨hm1, h2, hev, hLL1⟩)]
      have hlt := hL₀ L (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by rw [hfval]; exact Real.sqrt_nonneg _)] at hlt
      rw [← hfval]; exact hlt

end LatticeSystem.Quantum
