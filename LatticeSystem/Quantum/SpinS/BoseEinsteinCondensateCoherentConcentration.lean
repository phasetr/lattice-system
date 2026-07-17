import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensate

/-!
# Tasaki §5.3 Theorem 5.3: the `U(1)` coherent order-parameter concentration bound (AXIOM)

The final analytic input to the BEC `U(1)` symmetry-breaking Theorem 5.3 is the order-parameter
lower bound `m∗ ≥ √(2 q₀)` (Tasaki §5.3, "As in Theorem 4.11 (p. 101), we can prove the bound
`m∗ ≥ √(2 q₀)`.  See (4.2.39)", pp. 141–142).  The factor `√2` (rather than the `√3` of the
`SU(2)` Theorem 4.11) is the `U(1)` planar isotropy factor: the BEC order operator lives on the two
axes `α = 1, 2` only, so the base ratio saturates at `2 q₀`.

This module records that bound as a **documented axiom** `becMStar_ge_sqrt_twoQ`, the BEC
half-filling counterpart of the `SU(2)` concentration axiom
`orderSqMoment_ratio_le_mStarSq_family` (`AndersonTowerOrderSqConcentration.lean`) and of the
`p̂`-mirror `mStar_eq_phat_ratio_limit` (`OrderOperatorAlgebra.lean`).  Both those axioms pin `m∗`
to its genuine value through an `IsRealizingTanakaGroundStateFamily`; here the pinning is done by
the new `IsRealizingBECCoherentFamily` (the `U(1)` planar analogue: it drops the axis-`1` singlet
`Ŝ^{(1)}_tot Φ = 0` and reversal invariance that the `SU(2)` family carries, keeping only the
half-filling `Ŝ^{(3)}_tot Φ = 0`, so it is directly instantiable by the BEC ground state).

## Why the axiom is stated with `m∗` pinned by a realizing family (over-quantification safety)

If `m∗` were a free parameter one could take `m∗ := 0` together with a genuine long-range-ordered
family (`q₀ > 0`), making `√(2 q₀) ≤ 0` FALSE and `False` derivable (cf. the
`Axiom ∀ must hold for all` discipline; the `SU(2)` sibling documents the same trap).  We instead
pin `m∗` to the genuine coherent order parameter: `IsRealizingBECCoherentFamily` requires
`⟨Ξ_0, Ô^{(1)} Ξ_0⟩ / L^d → m∗` (eq. (5.3.7) at `θ = 0`), fixing `m∗` as the true SSB order
parameter.  The pinned bound `m∗ ≥ √(2 q₀)` is then the genuine "easy half" of the Koma–Tasaki
concentration mechanism (the base ratio `→ 2 q₀`); the matching *equality* `m∗² = 2 q₀`
(Conjecture 4.12's `U(1)` analogue) is a strictly stronger separate statement never asserted here.
The pinned family is unsatisfiable in `d = 1` (no LRO ground state, Corollary 4.3), so the axiom is
vacuous there.

Reference: Koma, Tasaki, *Symmetry breaking and finite-size effects in quantum many-body systems*,
J. Stat. Phys. **76** (1994) 745–803 [66] (concentration mechanism); Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems* (1st ed., Springer, 2020), §5.3, Theorem 5.3, `m∗ ≥
√(2 q₀)` via eq. (4.2.39), pp. 141–142 (BEC construction proved in Koma–Tasaki [21]).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **A realizing BEC coherent family** (Tasaki §5.3, the `U(1)` planar analogue of
`IsRealizingTanakaGroundStateFamily`).  It bundles a half-filling hard-core boson ground-state
family `Φ L` at chemical potential `μ = 0`, together with a slow window `M_win`, so that the order
parameter `m∗` is *pinned* to the genuine coherent order parameter and cannot be a free variable.

For a slowly diverging window (`Tendsto M_win atTop atTop`), eventually in even `L`:
* `Φ L` is a nonzero minimizer of the `μ = 0` chemical-potential XY Hamiltonian
  (`xyChemicalPotentialHamiltonianS d L 0`);
* `Φ L` sits at half filling (`Ŝ^{(3)}_tot Φ = 0`; unlike the `SU(2)` family, axis-`1` singlet and
  reversal invariance are **not** imposed — BEC ground states are `U(1)` planar, not `SU(2)`);
* the two planar axes carry ODLRO with constant `q₀` (`⟨(Ô^{(α)})²⟩ / V² ≥ q₀`, `α = 1, 2`);
* the tower states are nonzero across the window (`|M| ≤ C₁ L^{d/2}`), so the `Γ_M` normalize.

The **pinning conjunct** fixes `m∗` as the exact coherent order parameter: at `θ = 0` the
coherent-state moment density converges, `⟨Ξ_0, Ô^{(1)} Ξ_0⟩ / L^d → m∗` (eq. (5.3.7) at
`θ = 0`, `cos 0 = 1`).  Together with `0 < m∗` this makes `m∗` the genuine SSB order parameter, the
value the documented axiom `becMStar_ge_sqrt_twoQ` bounds below by `√(2 q₀)`. -/
def IsRealizingBECCoherentFamily (d : ℕ) (q₀ mStar C₁ : ℝ)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ) (Mwin : ℕ → ℕ) : Prop :=
  Filter.Tendsto Mwin Filter.atTop Filter.atTop ∧
  (∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
    (xyChemicalPotentialHamiltonianS d L 0).mulVec (Φ L) = E₀ L • Φ L ∧
    (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin 2) → ℂ, Ψ ≠ 0 →
      (xyChemicalPotentialHamiltonianS d L 0).mulVec Ψ = E • Ψ → (E₀ L).re ≤ E.re) ∧
    Φ L ≠ 0 ∧
    (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec (Φ L) = 0 ∧
    (∀ α : Fin 3, α ≠ 2 → q₀ ≤ expectationRatioRe
      ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2) ∧
    (∀ M : ℤ, (M.natAbs : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
      towerState (torusParitySublattice d L) 1 M (Φ L) ≠ 0)) ∧
  (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
    |expectationRatioRe (staggeredOrderOp1S (torusParitySublattice d L) 1)
        (becCoherentState d L 0 (Mwin L) (Φ L)) / (L : ℝ) ^ d - mStar| < ε) ∧
  0 < mStar

/-- **Tasaki Theorem 5.3 (the `U(1)` order-parameter lower bound `m∗ ≥ √(2 q₀)`), AXIOM.**  Tasaki
§5.3 states "As in Theorem 4.11 (p. 101), we can prove the bound `m∗ ≥ √(2 q₀)`.  See (4.2.39)"
(pp. 141–142): the BEC coherent order parameter `m∗` is bounded below by `√(2 q₀)`, the `U(1)`
planar (`√2`) counterpart of the `SU(2)` (`√3`) bound of Theorem 4.11.

This is the BEC half-filling counterpart of the `SU(2)` concentration axiom
`orderSqMoment_ratio_le_mStarSq_family` and of the `p̂`-mirror `mStar_eq_phat_ratio_limit`; per the
2026-07-12 no-overreach boundary the Koma–Tasaki [66] concentration mechanism is deferred with
parity to those axioms rather than rebuilt.  `m∗` is **pinned** to its genuine value by
`IsRealizingBECCoherentFamily` (`hFamily`): the coherent moment density converges to `m∗`
(eq. (5.3.7) at `θ = 0`), so `m∗` is the true SSB order parameter and the bound is the genuine
"easy half" (`m∗² ≥ 2 q₀`) of [66], never the still-open equality `m∗² = 2 q₀`.  A free `m∗`
would make the statement FALSE (`m∗ := 0` with `q₀ > 0`), hence the family pinning.  The family is
unsatisfiable in `d = 1` (Corollary 4.3), so the axiom is vacuous there. -/
axiom becMStar_ge_sqrt_twoQ (d : ℕ) (hd : 1 ≤ d) (q₀ mStar C₁ : ℝ)
    (hq₀ : 0 < q₀) (hC₁ : 0 < C₁)
    (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ) (Mwin : ℕ → ℕ)
    (hFamily : IsRealizingBECCoherentFamily d q₀ mStar C₁ Φ E₀ Mwin) :
    Real.sqrt (2 * q₀) ≤ mStar

end LatticeSystem.Quantum
