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

Here `R_k = orderSqMoment d L N Φ k` and `V² = (L^d)²`; `hR` (eventual moment positivity, `∃ Lr`,
matching the eventual form of `hsinglet`/`hlim3`) makes the division meaningful, corresponding to
the `p̂` mirror's `hPhat`. -/
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
    (hR : ∃ Lr : ℕ, ∀ (n L : ℕ) [NeZero L], Lr ≤ L → 2 ≤ L → Even L →
      0 < orderSqMoment d L N (Φ L) n) :
    ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      orderSqMoment d L N (Φ L) (n + 1) /
          (orderSqMoment d L N (Φ L) n * ((L : ℝ) ^ d) ^ 2) < mStar ^ 2 + ε

open Filter in
/-- **Tasaki Theorem 4.11 core: the `n = 0` `ô²`-moment concentration upper bound, `hFamily`-pinned,
`hconj`-free, AXIOM.**  §4.2.2 eqs. (4.2.59)–(4.2.61) (pp. 105–109) instruct the reader to *repeat
the `p̂` argument* (elementary, proof omitted, see [66]/Koma–Tasaki) for the `ô²` field, giving the
`n = 0` instance of the successive-ratio bound: for every `ε > 0`, eventually in (even) `L`, the
`V²`-normalised base ratio `s₀ = R₁/(R₀·V²) = ⟨Φ, ô² Φ⟩/(‖Φ‖² V²)` stays below `(m∗)² + ε`, i.e.
`lim_L s₀(L) ≤ (m∗)²`.  Here `R_k = orderSqMoment d L N Φ k` and `V² = (L^d)²`.

**`SU(2)`/`ô²` parity of the `p̂`/`U(1)` mirror.**  This is the `SU(2)`/`√3` parity companion of the
already-recorded `p̂`/`U(1)` documented axiom `mStar_eq_phat_ratio_limit`
(`OrderOperatorAlgebra.lean`), which pins the *same* `m∗` by a `IsRealizingTanakaGroundStateFamily`
and records the `√(2 q₀) ≤ m∗` (`U(1)`, `√2`) bound; here we record the `ô²`-field concentration
whose base ratio `→ 3 q₀` (isotropy factor `3`) drives Theorem 4.11's `√(3 q₀) ≤ m∗` (`SU(2)`, `√3`)
under the 2026-07-12 no-overreach boundary.

**Why the naive `hconj`-drop is UNSOUND (so `m∗` must be pinned by `hFamily`).**  One cannot simply
delete the `hconj : IsConjecture412Equality mStar qStar` hypothesis from the sibling axiom
`orderSqMoment_ratio_le_mStarSq`: with `hconj` gone, `m∗` is a *free* parameter unconstrained by
`Φ`.  Taking `mStar := 0` while `Φ` is a genuine long-range-ordered singlet (`qStar > 0`) satisfies
`hsinglet`/`hlim3`/`hR` yet the base ratio gives `s₀ → 3 qStar > 0`, contradicting the claimed
`s₀ < 0 + ε`; so the naively `hconj`-dropped statement is FALSE (`False` derivable, cf. the
`Axiom ∀ must hold for all` discipline).  We instead pin `m∗` to its genuine value via
`IsRealizingTanakaGroundStateFamily` (`hFamily`): the exact staggered-moment limit (`m∗`) together
with `IsTanakaFullSSBConstants` fixes `m∗` as the true order parameter, exactly as the `p̂` mirror
does.

**Why this pinned statement is TRUE (and Conjecture 4.12-independent).**  With `m∗` pinned to the
genuine order parameter, `s₀ ≤ (m∗)²` is the true content of [66]: the `V²`-normalised `ô²`-moment
ratio saturates from below at the squared SSB order parameter `(m∗)²`, so its `n = 0` value is
bounded above by `(m∗)²`.  This is only the "easy half" (`≥`, i.e. `(m∗)² ≥ 3 q₀`) of Theorem 4.11;
the matching *equality* `(m∗)² = 3 q₀` is the still-open Conjecture 4.12, a strictly stronger and
separate statement never asserted here.  The pinned family is unsatisfiable in `d = 1` (no LRO
ground state, Corollary 4.3), so the axiom is vacuous there.

Reference: Koma, Tasaki, *Symmetry breaking and finite-size effects in quantum many-body systems*,
J. Stat. Phys. **76** (1994) 745–803 [66]; Hal Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems* (1st ed., Springer, 2020), §4.2.2, Theorem 4.11, eq. (4.2.23),
eqs. (4.2.59)–(4.2.61), pp. 101, 105–109. -/
axiom orderSqMoment_ratio_le_mStarSq_family (d N : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hq₀ : 0 < q₀) (hC₁ : 0 < C₁)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ) (M : ℕ → ℕ)
    (hFamily : IsRealizingTanakaGroundStateFamily d N q₀ mStar C₁ Φ E₀ M) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
      orderSqMoment d L N (Φ L) 1 /
          (orderSqMoment d L N (Φ L) 0 * ((L : ℝ) ^ d) ^ 2) < mStar ^ 2 + ε

end LatticeSystem.Quantum
