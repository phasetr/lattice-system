import LatticeSystem.Quantum.SpinS.AndersonTower
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tasaki §4.2: solid-angle average of the symmetry-breaking states (Proposition 4.10)

For a unit vector `n ∈ S² ⊂ ℝ³`, the direction order operator `Ô_L^n = Σ_x ε_x (Ŝ_x · n)` defines a
direction symmetry-breaking state `|Ξ_n⟩` (eq. (4.2.17)) exactly as `|Ξ_{(1,0,0)}⟩`.  By `SU(2)`
covariance `Û|Ξ_n⟩ = |Ξ_{Rn}⟩` (eq. (4.2.19)), the solid-angle average
`(1/4π) ∫_{|n|=1} dn |Ξ_n⟩` is `SU(2)` invariant (eq. (4.2.20)), and one conjectures it is
proportional to the unique ground state `|Φ_GS⟩` (eq. (4.2.21)).

**Proposition 4.10** (eq. (4.2.22)) makes this precise *conditionally*: assuming the conjectured
equality `m∗ = √(3 q∗)` of Conjecture 4.12, the normalized solid-angle average converges to `|Φ_GS⟩`
(up to phase) as `L ↑ ∞`.

We record it as a documented axiom.  Following the established design: the solid-angle average is
the Bochner integral over the unit sphere in `EuclideanSpace ℝ (Fin 3)` with the surface measure
`volume.toSphere` (`solidAngleAverageTanaka`); Conjecture 4.12 is an explicit `Prop` hypothesis
(`IsConjecture412Equality`, never asserted as true here); the convergence is stated up to a
unimodular phase (`Φ_GS` is only defined up to phase); and it is conditional on long-range order
(vacuous in one dimension by Corollary 4.3).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1, Proposition 4.10, eqs. (4.2.17)–(4.2.22), pp. 99–100.
-/

namespace LatticeSystem.Quantum

open Matrix MeasureTheory Filter

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **direction order operator** `Ô_L^n = Σ_x ε_x (Ŝ_x · n)` for a unit vector
`n ∈ EuclideanSpace ℝ (Fin 3)` and a sublattice assignment `A` (`ε_x = ±1`).  For `n = (1,0,0)`
it is `staggeredOrderOp1S`. -/
noncomputable def directionStaggeredOp (n : EuclideanSpace ℝ (Fin 3)) (A : Λ → Bool) (N : ℕ) :
    ManyBodyOpS Λ N :=
  ∑ x : Λ, (if A x then (1 : ℂ) else (-1 : ℂ)) •
    (((n 0 : ℝ) : ℂ) • spinSSiteOp1 x N + ((n 1 : ℝ) : ℂ) • spinSSiteOp2 x N +
      ((n 2 : ℝ) : ℂ) • spinSSiteOp3 x N)

/-- The (unnormalized) `k`-th direction tower term `(Ô_L^n)^k Φ`. -/
noncomputable def directionTanakaTowerTerm (n : EuclideanSpace ℝ (Fin 3)) (A : Λ → Bool) (N k : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) : (Λ → Fin (N + 1)) → ℂ :=
  ((directionStaggeredOp n A N) ^ k).mulVec Φ

/-- The **direction symmetry-breaking state** `|Ξ_n⟩` (eq. (4.2.17)): the normalized sum of two
adjacent direction tower terms (each separately unit-normalized, global `1/√2`).  For `n = (1,0,0)`
it reduces to `tanakaSSBState`. -/
noncomputable def directionTanakaState (n : EuclideanSpace ℝ (Fin 3)) (A : Λ → Bool) (N M : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) : (Λ → Fin (N + 1)) → ℂ :=
  ((Real.sqrt (2 : ℝ) : ℂ))⁻¹ •
    (unitNormalize (directionTanakaTowerTerm n A N M Φ) +
      unitNormalize (directionTanakaTowerTerm n A N (M + 1) Φ))

/-- The **solid-angle average** `∫_{|n|=1} |Ξ_n⟩ dn` of the direction symmetry-breaking states, as a
Bochner integral over the unit sphere in `EuclideanSpace ℝ (Fin 3)` with the surface measure
`volume.toSphere` (eq. (4.2.20)–(4.2.21)).  The overall normalization (`4π`) is immaterial: it is
absorbed by the `unitNormalize` and the up-to-phase comparison in Proposition 4.10. -/
noncomputable def solidAngleAverageTanaka (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) : (HypercubicTorus d L → Fin (N + 1)) → ℂ :=
  ∫ n : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
    directionTanakaState (n : EuclideanSpace ℝ (Fin 3)) (torusParitySublattice d L) N M Φ
      ∂(MeasureTheory.volume.toSphere)

/-- **Conjecture 4.12 (eq. (4.2.26)), core equality as a `Prop`** (never asserted true): the
symmetry-breaking order parameter and the long-range-order parameter coincide, `m∗ = √(3 q∗)`. -/
def IsConjecture412Equality (mStar qStar : ℝ) : Prop :=
  mStar = Real.sqrt (3 * qStar)

/-- **Tasaki Conjecture 4.12 (the SSB and LRO order parameters coincide), as a `Prop` STATEMENT
ONLY** (eqs. (4.2.25)–(4.2.26)).  This registers the *unproven* conjecture as a numbered, searchable
item; it is a `def … : Prop` and is **never asserted true** (no `axiom`/`theorem` derives it — that
would be unsound, the conjecture being open).

The statement: for the `d`-dimensional hypercubic antiferromagnetic Heisenberg model, whenever a
genuine realizing ground-state family `Φ` (eventual minimizer, nonzero, well-defined Tanaka terms,
realizing slowly-diverging tower `M`) has long-range-order limit `q∗` (`hLRO`, eq. (4.2.25)) and the
Tanaka state has staggered-moment limit `m∗` (`hSSB`, eq. (4.2.12)) with `m∗` the genuine SSB order
parameter (`IsTanakaFullSSBConstants`), then `m∗ = √(3 q∗)` (eq. (4.2.26)).  Tasaki believes this is
very likely valid but it is far from proven; we record it without asserting it. -/
def conjecture_4_12 (d N : ℕ) : Prop :=
  ∀ (q₀ mStar C₁ : ℝ), 0 < q₀ → 0 < C₁ →
    ∀ (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ) (M : ℕ → ℕ),
      Tendsto M atTop atTop →
      (∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec (Φ L) = E₀ L • Φ L ∧
        (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
          (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ → (E₀ L).re ≤ E.re) ∧
        Φ L ≠ 0 ∧
        0 < M L ∧ ((M L : ℝ) + 1) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) ∧
        0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M L) (Φ L)) ∧
        0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M L + 1) (Φ L)) ∧
        0 < vecNormSqRe (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L))) →
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        |(star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
            staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
            ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2) - q₀| < ε) →
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        |tanakaOrderMean1 d L N (M L) (Φ L) - mStar| < ε) →
      IsTanakaFullSSBConstants d N q₀ C₁ mStar →
      IsConjecture412Equality mStar q₀

/-- The Proposition 4.10 statement for fixed constants.  For a given ground-state family `Φ` (with
the minimizer / long-range-order conditions eventual) and the *actual* long-range-order limit
`qStar`
of that family (`q∗`, eq. (4.2.25), pinned by `Φ` — not freely chosen), **conditional on
Conjecture 4.12** (`m∗ = √(3 qStar)`, a genuine hypothesis tying `m∗` to the physical `q∗`):
there is a slowly diverging `M(L)` such that the *normalized solid-angle average* of the
symmetry-breaking states converges, up to a unimodular phase, to the ground state (eq. (4.2.22)):
`∀ ε > 0, ∃ L₀, ∀ L ≥ L₀ (even), ∃ z, ‖z‖ = 1 ∧ √(vecNormSqRe(unitNormalize(Ξ_avg) − z • Φ̂)) < ε`
(the distance is the **L²/Hilbert** norm `√⟨·,·⟩`, via `vecNormSqRe`, not the default sup norm). -/
def IsTanakaSphereAverageConstants (d N : ℕ) (q₀ C₁ mStar : ℝ) : Prop :=
  0 < C₁ ∧ 0 < mStar ∧
    (∀ (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ),
      (∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec (Φ L) = E₀ L • Φ L ∧
        (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
          (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ → (E₀ L).re ≤ E.re) ∧
        Φ L ≠ 0 ∧
        q₀ ≤ (star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
            staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
            ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2)) →
      -- `qStar` is the *actual* long-range-order limit `q∗` of this ground-state family
      -- (eq. (4.2.25)); it is determined by `Φ`, not freely chosen
      ∀ qStar : ℝ,
        (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
          |(star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
              staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
              ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2) - qStar| < ε) →
        -- Conjecture 4.12 (eq. (4.2.26)) relating the SSB and LRO order parameters
        IsConjecture412Equality mStar qStar →
        ∃ M : ℕ → ℕ, Tendsto M atTop atTop ∧
          (∃ L₂ : ℕ, ∀ (L : ℕ) [NeZero L], L₂ ≤ L → 2 ≤ L → Even L →
            0 < M L ∧ ((M L : ℝ) + 1) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2)) ∧
          ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
            ∃ z : ℂ, ‖z‖ = 1 ∧
              Real.sqrt (vecNormSqRe (unitNormalize (solidAngleAverageTanaka d L N (M L) (Φ L)) -
                z • unitNormalize (Φ L))) < ε)

/-- **Tasaki Proposition 4.10 (the solid-angle average is the ground state), AXIOM.**  Assuming
Conjecture 4.12 (`m∗ = √(3 q∗)`), the normalized solid-angle average of the symmetry-breaking states
`|Ξ_n⟩` converges (up to phase) to the unique ground state `|Φ_GS⟩` as `L ↑ ∞` (eq. (4.2.22)): the
`SU(2)`-symmetric average of the symmetry-breaking "ground states" recovers the LRO-but-no-SSB
ground state.

The axiom asserts `IsTanakaFullSSBConstants d N q₀ C₁ mStar` (Theorem 4.9) alongside, so `mStar` is
the *same* full-SSB order parameter — letting downstream code combine Proposition 4.10 with
Theorem 4.9 for one physical order parameter.

Recorded as a documented axiom, sharing constants `C₁`, `C₂`, `m∗` with the Anderson-tower /
full-SSB statements and conditional on long-range order (vacuous in one dimension by Corollary 4.3).
Conjecture 4.12 enters only as a hypothesis (`IsConjecture412Equality`); never asserted true. -/
axiom tanakaSphereAverage_groundState (d N : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ mStar : ℝ, IsAndersonTowerConstants d N q₀ C₁ C₂ ∧
      IsTanakaSSBConstants d N q₀ C₁ C₂ ∧
      IsTanakaFullSSBConstants d N q₀ C₁ mStar ∧
      IsTanakaSphereAverageConstants d N q₀ C₁ mStar

end LatticeSystem.Quantum
