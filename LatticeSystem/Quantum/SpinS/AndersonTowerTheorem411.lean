import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSqConcentration

/-!
# Tasaki §4.2.2 Theorem 4.11 (the two order parameters) — discharged capstone

This module proves **Tasaki, Theorem 4.11, eq. (4.2.23), p. 101** (Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer, 2020): the symmetry-breaking order
parameter `m∗` and the long-range-order parameter `q₀` of a realizing Tanaka ground-state family
satisfy `√(3 q₀) ≤ m∗`.  The factor `√3` reflects the `SU(2)` symmetry of the Heisenberg
model (for the `U(1)`/XXZ variant it is `√2`, Lemma 4.15).

The former axiom `tanakaSSB_orderParameter_lowerBound` (in `AndersonTower.lean`) is replaced by this
proved `theorem` of the *same* signature.  The proof assembles two already-established facts about
the `V²`-normalised base `ô²`-moment ratio `s₀(L) = R₁ / (R₀ · V²)`
(`R_k = orderSqMoment d L N (Φ L) k`, `V = L^d`):

* the **Conjecture-4.12-free** base-ratio limit `s₀(L) → 3 q₀`
  (`orderSqMoment_baseRatio_tendsto_threeQ`, PR-1), driven by the factor-3 diagonal isotropy on the
  total-spin singlet; and
* the **documented concentration axiom** `s₀(L) < (m∗)² + ε` eventually
  (`orderSqMoment_ratio_le_mStarSq_family`, PR-2), the `SU(2)`/`ô²` parity companion of the
  `p̂`/`U(1)` mirror `mStar_eq_phat_ratio_limit`, recording the `[66]` concentration bound with
  `m∗` pinned by `IsRealizingTanakaGroundStateFamily`.

Comparing the two limits gives `3 q₀ ≤ (m∗)²`; √-monotonicity with `m∗ > 0` (Theorem 4.9)
yields the bound.  **Conjecture 4.12** (`(m∗)² = 3 q₀`, eq. (4.2.26)) is *not* used: only
the "easy half" (`≥`) of the equality.

`#print axioms tanakaSSB_orderParameter_lowerBound` therefore lists the standard three
(`propext`, `Classical.choice`, `Quot.sound`) plus the single documented concentration axiom
`orderSqMoment_ratio_le_mStarSq_family`; `IsConjecture412Equality` does *not* appear.

Reference: Hal Tasaki, §4.2.2, Theorem 4.11, eq. (4.2.23), p. 101; proof machinery
eqs. (4.2.57)–(4.2.61), pp. 105–109; Koma, Tasaki, J. Stat. Phys. **76** (1994) 745–803 [66].
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Tasaki Theorem 4.11 (the two order parameters), eq. (4.2.23), p. 101.**  For a
realizing Tanaka ground-state family (hFamily : IsRealizingTanakaGroundStateFamily
d N q₀ mStar C₁ Φ E₀ M), the order parameters satisfy `√(3 q₀) ≤ m∗`. The factor
`√3` reflects `SU(2)` symmetry.

Proof: the base `ô²`-moment ratio `s₀(L) = R₁/(R₀·V²)` tends to `3 q₀`
(`orderSqMoment_baseRatio_tendsto_threeQ`, singlet factor-3 isotropy, Conjecture-4.12-free),
while it is eventually `< (m∗)² + ε` for every `ε > 0`
(`orderSqMoment_ratio_le_mStarSq_family`, the
documented `SU(2)`/`ô²` concentration axiom pinned by `hFamily`).  Comparing the two limits
forces `3 q₀ ≤ (m∗)²`, √-monotonicity (Theorem 4.9) yields the bound.  Only the "easy half"
(`≥`) of Conjecture 4.12
(`(m∗)² = 3 q₀`, eq. (4.2.26)), which is *not* assumed.  The family is unsatisfiable in
`d = 1`
(no long-range-ordered ground state, Corollary 4.3), so the bound applies exactly where it should.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, Theorem 4.11, eq. (4.2.23), p. 101; Koma, Tasaki, J. Stat. Phys. **76** (1994)
745–803 [66]. -/
theorem tanakaSSB_orderParameter_lowerBound (d N : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hq₀ : 0 < q₀) (hC₁ : 0 < C₁)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ)
    (M : ℕ → ℕ)
    (hFamily : IsRealizingTanakaGroundStateFamily d N q₀ mStar C₁ Φ E₀ M) :
    Real.sqrt (3 * q₀) ≤ mStar := by
  -- Extract the family parts by projection (keeping `hFamily` intact for the concentration axiom):
  -- the eventual-singlet block (`.2.1`), the axis-3 LRO limit `→ q₀` (`.2.2.1`), and the
  -- full-SSB constants `.2.2.2.2` (which supply `0 < m∗`).
  obtain ⟨L₁, hEv⟩ := hFamily.2.1
  have hlim3 := hFamily.2.2.1
  have hFull := hFamily.2.2.2.2.1
  -- Eventual total-spin-singlet property, projected out of the family block (conjuncts 4 and 5).
  have hsinglet : ∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
      (totalSpinSOp3 (HypercubicTorus d L) N).mulVec (Φ L) = 0 ∧
        (totalSpinSOp1 (HypercubicTorus d L) N).mulVec (Φ L) = 0 :=
    ⟨L₁, fun L _ hL h2 hev => ⟨(hEv L hL h2 hev).2.2.2.1, (hEv L hL h2 hev).2.2.2.2.1⟩⟩
  -- (A) Conjecture-4.12-free base-ratio limit `s₀(L) → 3 q₀` (factor-3 isotropy, PR-1).
  have hbase := orderSqMoment_baseRatio_tendsto_threeQ d N Φ hsinglet q₀ hlim3
  -- (B) Documented `SU(2)`/`ô²` concentration axiom `s₀(L) < (m∗)² + ε` eventually (PR-2).
  have hconc := orderSqMoment_ratio_le_mStarSq_family d N hd q₀ mStar C₁ hq₀ hC₁ Φ E₀ M
    hFamily
  -- (C) Compare the two limits: `3 q₀ ≤ (m∗)²`.
  have hle : 3 * q₀ ≤ mStar ^ 2 := by
    by_contra hcon
    rw [not_le] at hcon
    -- With `(m∗)² < 3 q₀`, split the gap: `ε = (3 q₀ − (m∗)²)/2 > 0`.
    set ε : ℝ := (3 * q₀ - mStar ^ 2) / 2 with hεdef
    have hε : 0 < ε := by rw [hεdef]; linarith
    obtain ⟨L₀a, hbaseε⟩ := hbase ε hε
    obtain ⟨L₀b, hconcε⟩ := hconc ε hε
    -- Pick an even `L ≥ 2` beyond both thresholds.
    set L : ℕ := 2 * (max L₀a L₀b + 1) with hLdef
    haveI : NeZero L := ⟨by omega⟩
    have hEven : Even L := ⟨max L₀a L₀b + 1, by omega⟩
    have hb := hbaseε L (by omega) (by omega) hEven
    have hc := hconcε L (by omega) (by omega) hEven
    rw [abs_lt] at hb
    -- `3 q₀ − ε < s₀ < (m∗)² + ε` with `2 ε = 3 q₀ − (m∗)²` is contradictory.
    rw [hεdef] at hb hc
    linarith [hb.1, hc]
  -- (D) `√`-monotonicity with `m∗ > 0` (full-SSB constants, Theorem 4.9).
  have hmStar : 0 < mStar := hFull.2.1
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq hmStar.le] at this

end LatticeSystem.Quantum
