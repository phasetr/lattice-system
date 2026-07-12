import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSqBaseRatio

/-!
# Tasaki §4.2.2 Proposition 4.10 (L5-b-ii): the `ô²`-moment concentration upper bound (AXIOM)

The concentration (upper) step of the `ô²`-moment collapse driving Proposition 4.10.  With the
`ô²`-moments `R_k := orderSqMoment d L N Φ k = ⟨Φ, (ô²)^k Φ⟩`, `V² := (L^d)²` and the
`V²`-normalised successive ratio `s_n := R_{n+1} / (R_n · V²)`, this module records the
**documented axiom**

`∀ n, ∀ ε > 0, eventually in (even) L,  s_n < (m∗)² + ε`   (`orderSqMoment_ratio_le_mStarSq`),

i.e. the `limsup`-**upper** direction of `lim_n lim_L s_n = (m∗)²`.

## Why this is a documented axiom (no-overreach boundary 2026-07-12)

Tasaki proves the analogous `p̂`-field concentration only by *citing* it: §4.2.2 eq. (4.2.40)
states the `p̂`-ratio concentration is "elementary, proof omitted; see [66]" (Koma–Tasaki), and
eqs. (4.2.59)–(4.2.61) then instruct the reader to *repeat the `p̂` argument* for the `ô²` field,
yielding `lim_n lim_L ⟨(ô²)^{n+1}⟩/(⟨(ô²)^n⟩·V²) = (m∗)²`.  The `p̂`-side mirror
`mStar_eq_phat_ratio_limit` (`OrderOperatorAlgebra.lean:908`) is already recorded as a documented
axiom.  Per the 2026-07-12 no-overreach boundary (preventing both omission and overreach), this
`ô²` concentration sub-arc is deferred **with parity** to that `p̂` mirror rather than rebuilding
the 6–9 PR [66]/Koma–Tasaki concentration machinery; Conjecture 4.12 stays an explicit hypothesis,
never asserted true.

Reference: Koma, Tasaki, *Symmetry breaking and finite-size effects in quantum many-body systems*,
J. Stat. Phys. **76** (1994) 745–803 [66]; Hal Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems* (1st ed., Springer, 2020), §4.2.2, Proposition 4.10, eqs. (4.2.40),
(4.2.59)–(4.2.61), pp. 105–109.
-/

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

open Filter in
/-- **Tasaki Lemma 4.15 for the `ô²` field (ground-state `ô²`-moment concentration upper bound),
AXIOM.**  §4.2.2 eq. (4.2.40) states the `p̂` concentration "elementary, proof omitted; see [66]"
(Koma–Tasaki); eqs. (4.2.59)–(4.2.61) then say to *repeat the `p̂` argument* for the `ô²` field,
giving `lim_n lim_L ⟨(ô²)^{n+1}⟩/(⟨(ô²)^n⟩·V²) = (m∗)²`.  The `p̂`-side mirror
`mStar_eq_phat_ratio_limit` (`OrderOperatorAlgebra.lean:908`) is already a documented axiom; per the
2026-07-12 no-overreach boundary this `ô²` concentration sub-arc is deferred with parity to that
mirror.  We state only the `limsup`-**upper** direction actually consumed by the squeeze (the
`liminf`-lower is free from log-convexity plus the base ratio `orderSqMoment_baseRatio_tendsto`):
for every `n` and `ε > 0`, eventually in (even) `L`, the `V²`-normalised successive `ô²`-moment
ratio `s_n = R_{n+1}/(R_n·V²)` stays below `(m∗)² + ε`.  Conditional on Conjecture 4.12 (`hconj`,
never asserted), matching the base ratio's hypothesis surface (singlet family `hsinglet`, axis-3
long-range-order limit `hlim3 → q∗`, moment positivity `hR`); unsatisfiable in `d = 1` (no LRO,
Corollary 4.3), so vacuous there.

Here `R_k = orderSqMoment d L N Φ k` and `V² = (L^d)²`; `hR` (moment positivity) makes the division
meaningful, corresponding to the `p̂` mirror's `hPhat`. -/
axiom orderSqMoment_ratio_le_mStarSq (d N : ℕ) (hd : 1 ≤ d)
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
    (hR : ∀ (n L : ℕ) [NeZero L], 2 ≤ L → Even L → 0 < orderSqMoment d L N (Φ L) n) :
    ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      orderSqMoment d L N (Φ L) (n + 1) /
          (orderSqMoment d L N (Φ L) n * ((L : ℝ) ^ d) ^ 2) < mStar ^ 2 + ε

end LatticeSystem.Quantum
