import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSqIsotropy
import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSqMoment
import LatticeSystem.Quantum.SpinS.AndersonTowerSphereAverage

/-!
# Tasaki §4.2.2 Proposition 4.10 (L5-b-i): the base `ô²`-moment ratio limit

The base (concentration-independent) step of the `ô²`-moment collapse driving Proposition 4.10.
With the `ô²`-moments `R_k := orderSqMoment d L N Φ k = ⟨Φ, (ô²)^k Φ⟩` and `V² := (L^d)²`, this
module records the **exact base ratio limit** in two forms:

* the **Conjecture-free** limit `lim_{L → ∞} R_1 / (R_0 · V²) = 3 q∗`
  (`orderSqMoment_baseRatio_tendsto_threeQ`), which needs no hypothesis relating `m∗` and `q∗`;
* the derived limit `lim_{L → ∞} R_1 / (R_0 · V²) = (m∗)²`
  (`orderSqMoment_baseRatio_tendsto`), a one-line corollary of the former under Conjecture 4.12
  (`m∗ = √(3 q∗)`, an explicit hypothesis, never asserted true),

both for a total-spin-singlet ground-state family `Φ`.

The mechanism combines two ingredients and needs **no** concentration estimate and **no** the
Theorem 4.9 identity `m∗ = √q₀`:

* **factor-3 diagonal isotropy** (`orderSqOp_expectation_eq_three_mul_axis3`, eqs. (4.2.57)–
  (4.2.58)): on the singlet, `⟨Φ, ô² Φ⟩ = 3 · ⟨Φ, (ô^{(3)})² Φ⟩`, so `R_1 = 3 · ⟨(ô^{(3)})²⟩`;
* the **axis-3 long-range-order limit** `⟨(ô^{(3)})²⟩ / (‖Φ‖² V²) → q∗` (an explicit hypothesis,
  matching the conditioning of `IsTanakaSphereAverageConstants`).

Chaining these gives `R_1 / (R_0 · V²) = 3 · ⟨(ô^{(3)})²⟩ / (‖Φ‖² V²) → 3 q∗`; **Conjecture 4.12**
`(m∗)² = 3 q∗` (from `IsConjecture412Equality`) then upgrades `3 q∗` to `(m∗)²` in the corollary.
The Conjecture-free form is the one consumed by Theorem 4.11 (`√(3 q₀) ≤ m∗`), which carries no
Conjecture 4.12 hypothesis.

The limit is phrased as an `ε`–`δ` statement over even `L`, matching the axis-3 hypothesis and the
convergence layers of `IsTanakaSphereAverageConstants`, so it plugs directly into the geometric
moment squeeze (sequel L5-b-iii).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Proposition 4.10, eqs. (4.2.25)–(4.2.26), (4.2.57)–(4.2.59), pp. 105–109; Theorem
4.11, eq. (4.2.23), p. 101.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- **Conjecture-free base `ô²`-moment ratio limit** (Prop 4.10 L5-b-i / Theorem 4.11): for a
total-spin-singlet ground-state family `Φ` (eventual singlet `Ŝ³_tot Φ = Ŝ¹_tot Φ = 0`) whose
**axis-3** long-range-order ratio `⟨(ô^{(3)})²⟩ / (‖Φ‖² V²)` tends to `q∗` (`hlim3`), the full
`ô²`-moment base ratio tends to `3 q∗`:

`∀ ε > 0, ∃ L₀, ∀ L ≥ L₀ (even, ≥ 2), |R_1 / (R_0 · V²) − 3 q∗| < ε`,

where `R_k = orderSqMoment d L N Φ k` and `V² = (L^d)²`.  The proof uses only the factor-3 diagonal
isotropy `R_1 = 3 · ⟨(ô^{(3)})²⟩` on the singlet (eqs. (4.2.57)–(4.2.58)) and the axis-3 limit
`⟨(ô^{(3)})²⟩/(‖Φ‖²V²) → q∗`.  **No** hypothesis relating `m∗` and `q∗` (no Conjecture 4.12), **no**
concentration estimate, and **no** Theorem 4.9 identity `m∗ = √q₀` are used.  This is the form
consumed by Theorem 4.11 (`√(3 q₀) ≤ m∗`, eq. (4.2.23)), which carries no Conjecture 4.12
hypothesis. -/
theorem orderSqMoment_baseRatio_tendsto_threeQ (d N : ℕ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsinglet : ∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
      (totalSpinSOp3 (HypercubicTorus d L) N).mulVec (Φ L) = 0 ∧
        (totalSpinSOp1 (HypercubicTorus d L) N).mulVec (Φ L) = 0)
    (qStar : ℝ)
    (hlim3 : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      |(star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
          staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
          ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2) - qStar| < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      |orderSqMoment d L N (Φ L) 1 /
          (orderSqMoment d L N (Φ L) 0 * ((L : ℝ) ^ d) ^ 2) - 3 * qStar| < ε := by
  -- The `ε`–`δ` limit via the factor-3 bridge `R_1 = 3 · ⟨(ô^{(3)})²⟩`; no `m∗`/`q∗` tie needed.
  obtain ⟨L₁, hsing⟩ := hsinglet
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := hlim3 (ε / 3) (by linarith)
  refine ⟨max L₀ L₁, fun L _ hLge h2 hev => ?_⟩
  have hL₀le : L₀ ≤ L := le_trans (le_max_left _ _) hLge
  have hL₁le : L₁ ≤ L := le_trans (le_max_right _ _) hLge
  obtain ⟨h3, h1⟩ := hsing L hL₁le h2 hev
  have hR1 : orderSqMoment d L N (Φ L) 1
      = 3 * (star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
          staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re := by
    simp only [orderSqMoment, pow_one]
    rw [orderSqOp_expectation_eq_three_mul_axis3 (torusParitySublattice d L) (Φ L) h3 h1,
      Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  have hR0 : orderSqMoment d L N (Φ L) 0 = (star (Φ L) ⬝ᵥ Φ L).re := by
    simp only [orderSqMoment, pow_zero, Matrix.one_mulVec]
  have hbridge : orderSqMoment d L N (Φ L) 1 /
      (orderSqMoment d L N (Φ L) 0 * ((L : ℝ) ^ d) ^ 2)
      = 3 * ((star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
          staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
          ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2)) := by
    rw [hR1, hR0, mul_div_assoc]
  have haxis3 := hL₀ L hL₀le h2 hev
  have key : ∀ a : ℝ, |a - qStar| < ε / 3 → |3 * a - 3 * qStar| < ε := by
    intro a ha
    rw [show 3 * a - 3 * qStar = 3 * (a - qStar) from by ring, abs_mul,
      show |(3 : ℝ)| = 3 from by norm_num]
    linarith
  rw [hbridge]
  exact key _ haxis3

/-- **Base `ô²`-moment ratio limit** (Prop 4.10, L5-b-i): for a total-spin-singlet ground-state
family `Φ` (eventual singlet `Ŝ³_tot Φ = Ŝ¹_tot Φ = 0`) whose **axis-3** long-range-order ratio
`⟨(ô^{(3)})²⟩ / (‖Φ‖² V²)` tends to `q∗` (`hlim3`), **conditional on Conjecture 4.12**
(`m∗ = √(3 q∗)`, `hconj`, never asserted true), the full `ô²`-moment base ratio tends to `(m∗)²`:

`∀ ε > 0, ∃ L₀, ∀ L ≥ L₀ (even, ≥ 2), |R_1 / (R_0 · V²) − (m∗)²| < ε`,

where `R_k = orderSqMoment d L N Φ k` and `V² = (L^d)²`.  This is a one-line corollary of the
Conjecture-free limit `orderSqMoment_baseRatio_tendsto_threeQ` (`→ 3 q∗`) using
`(m∗)² = 3 q∗` (Conjecture 4.12): the nonnegativity `0 ≤ q∗` needed for `Real.sq_sqrt` is
recovered from `hlim3` (a limit of nonnegative positive-semidefinite ratios). -/
theorem orderSqMoment_baseRatio_tendsto (d N : ℕ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsinglet : ∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
      (totalSpinSOp3 (HypercubicTorus d L) N).mulVec (Φ L) = 0 ∧
        (totalSpinSOp1 (HypercubicTorus d L) N).mulVec (Φ L) = 0)
    (qStar mStar : ℝ)
    (hlim3 : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      |(star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
          staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
          ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2) - qStar| < ε)
    (hconj : IsConjecture412Equality mStar qStar) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      |orderSqMoment d L N (Φ L) 1 /
          (orderSqMoment d L N (Φ L) 0 * ((L : ℝ) ^ d) ^ 2) - mStar ^ 2| < ε := by
  -- `0 ≤ q∗` — the axis-3 ratios are nonnegative (positive-semidefinite `(ô^{(3)})²`), so their
  -- limit `q∗` is nonnegative.
  have hqStar : 0 ≤ qStar := by
    by_contra hneg
    rw [not_le] at hneg
    obtain ⟨L₀, hL₀⟩ := hlim3 (-qStar) (by linarith)
    set L := 2 * (L₀ + 1) with hLdef
    haveI : NeZero L := ⟨by omega⟩
    have hEven : Even L := ⟨L₀ + 1, by omega⟩
    have hbound := hL₀ L (by omega) (by omega) hEven
    have hnum : 0 ≤ (star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
        staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re := by
      have hSS : (staggeredOrderOpS (torusParitySublattice d L) N *
          staggeredOrderOpS (torusParitySublattice d L) N).PosSemidef := by
        have h := posSemidef_conjTranspose_mul_self
          (staggeredOrderOpS (torusParitySublattice d L) N)
        rwa [(staggeredOrderOpS_isHermitian _ N).eq] at h
      exact (Complex.le_def.mp (hSS.dotProduct_mulVec_nonneg (Φ L))).1
    have hden : 0 ≤ (star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2 :=
      mul_nonneg (Complex.le_def.mp (dotProduct_star_self_nonneg _)).1 (by positivity)
    have hratio : 0 ≤ (star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
        staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
        ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2) := div_nonneg hnum hden
    linarith [hratio, (abs_lt.mp hbound).2]
  -- `(m∗)² = 3 q∗` (Conjecture 4.12, `m∗ = √(3 q∗)`), then upgrade the Conjecture-free limit.
  have hmStar2 : mStar ^ 2 = 3 * qStar := by
    rw [hconj, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 3 * qStar)]
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := orderSqMoment_baseRatio_tendsto_threeQ d N Φ hsinglet qStar hlim3 ε hε
  refine ⟨L₀, fun L _ hLge h2 hev => ?_⟩
  rw [hmStar2]
  exact hL₀ L hLge h2 hev

end LatticeSystem.Quantum
