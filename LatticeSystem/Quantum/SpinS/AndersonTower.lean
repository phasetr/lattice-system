import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import LatticeSystem.Quantum.SpinS.DysonLiebSimon
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Tasaki §4.2: the "tower" of low-lying states (Theorem 4.6)

For the spin-`S` antiferromagnetic Heisenberg model on the `d`-dimensional hypercubic lattice with
long-range order, Tasaki constructs **Anderson's tower of low-lying states**.  Using the staggered
raising/lowering order operators `Ô_L^± = Σ_x (−1)^x Ŝ_x^±` (eq. (4.2.2)), the trial states
`Γ_M = (Ô_L^+)^M |Φ_GS⟩ / ‖·‖` (eq. (4.2.3)) lie in the `Ŝ_tot^{(3)} = M` sector and, for
`|M| ≤ C₁ L^{d/2}`, have energy within `C₂ M² / L^d` of the ground-state energy (Theorem 4.6,
eq. (4.2.4)):
`⟨Γ_M| Ĥ |Γ_M⟩ ≤ E_GS + C₂ M² / L^d`.
This `O(L^{d/2})` family of low-lying states is the rigorous form of Anderson's tower — the hallmark
of long-range order without spontaneous symmetry breaking.

To state Theorem 4.6 faithfully and soundly (a uniform constant `C₂` exists only for the genuine
translation-invariant hypercubic family, not for an arbitrary finite lattice), this file builds the
**`d`-dimensional hypercubic torus model**: the vertex set `Fin d → ZMod L` (`L^d` sites), the
nearest-neighbor coupling `torusNNCoupling`, and the parity (Néel) sublattice
`torusParitySublattice` (bipartite for even `L`).  The staggered raising/lowering operators are
defined for a general sublattice.  Theorem 4.6 is recorded as a documented axiom (the deep
reflection-positivity /
infinite-volume construction is deferred; infinite-volume systems are in scope).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.1, Theorem 4.6, eqs. (4.2.2)–(4.2.4), pp. 93–95 (Koma–Tasaki [35, 66]).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **staggered raising order operator** `Ô_L^+ = Σ_x ε_x Ŝ_x^+` (eq. (4.2.2)) for a sublattice
assignment `A` (`ε_x = ±1` the sublattice sign), built from the per-site raising operators
`spinSSiteOpPlus`. -/
noncomputable def staggeredRaisingOpS (A : Λ → Bool) (N : ℕ) : ManyBodyOpS Λ N :=
  ∑ x : Λ, (if A x then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpPlus x N

/-- The **staggered lowering order operator** `Ô_L^− = Σ_x ε_x Ŝ_x^−` (eq. (4.2.2)) for a sublattice
assignment `A`, built from the per-site lowering operators `spinSSiteOpMinus`. -/
noncomputable def staggeredLoweringOpS (A : Λ → Bool) (N : ℕ) : ManyBodyOpS Λ N :=
  ∑ x : Λ, (if A x then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOpMinus x N

/-- The **staggered `1`-axis order operator** `Ô_L^{(1)} = Σ_x ε_x Ŝ_x^{(1)}` for a sublattice
assignment `A`.  Since `Ŝ^{(1)} = (Ŝ^+ + Ŝ^−)/2`, this is `(Ô_L^+ + Ô_L^−)/2`; it is the order
operator whose direction `(1,0,0)` the Tanaka symmetry-breaking state singles out. -/
noncomputable def staggeredOrderOp1S (A : Λ → Bool) (N : ℕ) : ManyBodyOpS Λ N :=
  ∑ x : Λ, (if A x then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOp1 x N

/-- The **staggered `2`-axis order operator** `Ô_L^{(2)} = Σ_x ε_x Ŝ_x^{(2)}` for a sublattice
assignment `A`.  The `α = 3` staggered operator is the existing `staggeredOrderOpS`. -/
noncomputable def staggeredOrderOp2S (A : Λ → Bool) (N : ℕ) : ManyBodyOpS Λ N :=
  ∑ x : Λ, (if A x then (1 : ℂ) else (-1 : ℂ)) • spinSSiteOp2 x N

/-- The **real Rayleigh expectation** of an operator `O` at a vector `w`:
`expectationRatioRe O w = ⟨w, O w⟩.re / ⟨w, w⟩.re`.  Scale-invariant, so usable for states that are
not (proven to be) unit-normalized — in particular the Tanaka state. -/
noncomputable def expectationRatioRe {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℂ) (w : ι → ℂ) : ℝ :=
  (star w ⬝ᵥ O.mulVec w).re / (star w ⬝ᵥ w).re

/-- The squared `L²` norm of a vector, as a real number: `vecNormSqRe w = (⟨w, w⟩).re`.  Used as the
positive denominator in Rayleigh quotients and as the well-definedness witness for normalization. -/
noncomputable def vecNormSqRe {ι : Type*} [Fintype ι] (w : ι → ℂ) : ℝ :=
  (star w ⬝ᵥ w).re

/-- **Unit normalization** of a vector in the `L²` inner product: `unitNormalize w = ‖w‖⁻¹ • w`
(with `‖w‖ = √⟨w, w⟩`, and `0` when `w = 0`). -/
noncomputable def unitNormalize {ι : Type*} [Fintype ι] (w : ι → ℂ) : ι → ℂ :=
  ((Real.sqrt (vecNormSqRe w) : ℝ) : ℂ)⁻¹ • w

/-- The (unnormalized) `k`-th **Tanaka tower term** `(Ô_L^{(1)})^k Φ`, built with the `1`-axis
staggered order operator. -/
noncomputable def tanakaTowerTerm (A : Λ → Bool) (N k : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) : (Λ → Fin (N + 1)) → ℂ :=
  ((staggeredOrderOp1S A N) ^ k).mulVec Φ

/-- The **Tanaka symmetry-breaking state** `|Ξ_{(1,0,0)}⟩` (eq. (4.2.10)): the normalized sum of two
adjacent `1`-axis tower terms, each separately unit-normalized, with the global `1/√2`,
`|Ξ_{(1,0,0)}⟩ = (1/√2)( (Ô_L^{(1)})^M Φ / ‖·‖ + (Ô_L^{(1)})^{M+1} Φ / ‖·‖ )`.  Each term is
normalized on its own (faithful to (4.2.10)); the two terms lie in opposite-magnetization-parity
subspaces (orthogonal), and their interference magnifies the part of `Φ` with large positive
`Ô_L^{(1)}` — a candidate physical "ground state" with full `SU(2)` symmetry breaking in the
`(1,0,0)` direction. -/
noncomputable def tanakaSSBState (A : Λ → Bool) (N M : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) : (Λ → Fin (N + 1)) → ℂ :=
  ((Real.sqrt (2 : ℝ) : ℂ))⁻¹ •
    (unitNormalize (tanakaTowerTerm A N M Φ) + unitNormalize (tanakaTowerTerm A N (M + 1) Φ))

/-- The **Anderson tower trial state** `ψ_M = (Ô_L^{sgn M})^{|M|} Φ` (eq. (4.2.3), unnormalized):
for `M ≥ 0` apply the staggered *raising* operator `M` times, for `M < 0` apply the *lowering*
operator `|M|` times.  This realizes the two-sided tower `Γ_M`, `Γ_{−M}` in the
`Ŝ_tot^{(3)} = M` sectors. -/
noncomputable def towerState (A : Λ → Bool) (N : ℕ) (M : ℤ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) : (Λ → Fin (N + 1)) → ℂ :=
  ((if 0 ≤ M then staggeredRaisingOpS A N else staggeredLoweringOpS A N) ^ M.natAbs).mulVec Φ

/-- The **`d`-dimensional hypercubic torus** with side length `L`: the vertex set is
`Fin d → ZMod L`, a product of `d` cyclic groups, with `L^d` sites. -/
abbrev HypercubicTorus (d L : ℕ) : Type := Fin d → ZMod L

/-- The hypercubic torus `Fin d → ZMod L` has `L^d` sites. -/
theorem card_hypercubicTorus (d L : ℕ) [NeZero L] :
    Fintype.card (HypercubicTorus d L) = L ^ d := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The **nearest-neighbor coupling on the hypercubic torus**: `J x y = 1` when `x` and `y` differ
in exactly one coordinate by `±1` (cyclically), and `0` otherwise.  This is the periodic
nearest-neighbor antiferromagnetic Heisenberg interaction. -/
noncomputable def torusNNCoupling (d L : ℕ) [NeZero L]
    (x y : HypercubicTorus d L) : ℂ := by
  classical
  exact if (∃ i : Fin d, (∀ j, j ≠ i → x j = y j) ∧ (y i = x i + 1 ∨ y i = x i - 1)) then 1 else 0

/-- The **parity (Néel) sublattice** of the hypercubic torus: `A x = true` when the coordinate sum
`Σ_i (x i).val` is even.  Nearest neighbors differ in one coordinate by `±1`, flipping the parity,
so this bipartitions the torus (consistently for even `L`, where the wrap-around bonds also flip
parity). -/
def torusParitySublattice (d L : ℕ) [NeZero L] (x : HypercubicTorus d L) : Bool :=
  (∑ i : Fin d, (x i).val) % 2 = 0

/-- The **per-site staggered moment** `⟨Ξ| Ô_L^{(α)} |Ξ⟩ / L^d` of the Tanaka state in axis
`α = 1, 2, 3` (the order-operator density expectation), in Rayleigh-ratio form. -/
noncomputable def tanakaOrderMean1 (d L N : ℕ) [NeZero L] (M : ℕ)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) : ℝ :=
  expectationRatioRe (staggeredOrderOp1S (torusParitySublattice d L) N)
    (tanakaSSBState (torusParitySublattice d L) N M Φ) / (L : ℝ) ^ d

/-- The per-site staggered moment in axis `α = 2` (see `tanakaOrderMean1`). -/
noncomputable def tanakaOrderMean2 (d L N : ℕ) [NeZero L] (M : ℕ)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) : ℝ :=
  expectationRatioRe (staggeredOrderOp2S (torusParitySublattice d L) N)
    (tanakaSSBState (torusParitySublattice d L) N M Φ) / (L : ℝ) ^ d

/-- The per-site staggered moment in axis `α = 3` (using the existing `staggeredOrderOpS`). -/
noncomputable def tanakaOrderMean3 (d L N : ℕ) [NeZero L] (M : ℕ)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) : ℝ :=
  expectationRatioRe (staggeredOrderOpS (torusParitySublattice d L) N)
    (tanakaSSBState (torusParitySublattice d L) N M Φ) / (L : ℝ) ^ d

/-- The **per-site squared staggered moment** `⟨Ξ| (Ô_L^{(α)})² |Ξ⟩ / (L^d)²` of the Tanaka state in
axis `α = 1, 2, 3` (the order-operator-density-squared expectation), in Rayleigh-ratio form. -/
noncomputable def tanakaOrderSecond1 (d L N : ℕ) [NeZero L] (M : ℕ)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) : ℝ :=
  expectationRatioRe
    (staggeredOrderOp1S (torusParitySublattice d L) N *
      staggeredOrderOp1S (torusParitySublattice d L) N)
    (tanakaSSBState (torusParitySublattice d L) N M Φ) / ((L : ℝ) ^ d) ^ 2

/-- The per-site squared staggered moment in axis `α = 2` (see `tanakaOrderSecond1`). -/
noncomputable def tanakaOrderSecond2 (d L N : ℕ) [NeZero L] (M : ℕ)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) : ℝ :=
  expectationRatioRe
    (staggeredOrderOp2S (torusParitySublattice d L) N *
      staggeredOrderOp2S (torusParitySublattice d L) N)
    (tanakaSSBState (torusParitySublattice d L) N M Φ) / ((L : ℝ) ^ d) ^ 2

/-- The per-site squared staggered moment in axis `α = 3` (see `tanakaOrderSecond1`). -/
noncomputable def tanakaOrderSecond3 (d L N : ℕ) [NeZero L] (M : ℕ)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) : ℝ :=
  expectationRatioRe
    (staggeredOrderOpS (torusParitySublattice d L) N *
      staggeredOrderOpS (torusParitySublattice d L) N)
    (tanakaSSBState (torusParitySublattice d L) N M Φ) / ((L : ℝ) ^ d) ^ 2

/-- **Tasaki Theorem 4.6 (Anderson's tower of low-lying states), AXIOM.**  Fix the spin `S = N/2`
and a dimension `d ≥ 1`.  There are positive constants `C₁`, `C₂` (depending only on `d`, `S`, and
the long-range-order parameter `q₀`) such that, on every `d`-dimensional hypercubic torus of even
side `L ≥ 2`, for the antiferromagnetic nearest-neighbor Heisenberg model with ground state `Φ`
(energy `E₀`) and every `M` with `M ≤ C₁ L^{d/2}` for which the tower state
`ψ_M = (Ô_L^+)^M Φ` is nonzero (well-defined), the Rayleigh energy of `ψ_M` obeys (eq. (4.2.4)):
`⟨ψ_M, Ĥ ψ_M⟩ / ⟨ψ_M, ψ_M⟩ ≤ E₀ + C₂ M² / L^d`.

The Rayleigh-quotient (ratio) form makes the bound scale-invariant, so no separate normalization of
`ψ_M` is needed.  The uniform constant `C₂` exists precisely because the family is the genuine
translation-invariant hypercubic torus.

The theorem is **conditional on long-range order**: the constants depend on the LRO parameter
`q₀ > 0`, and the bound is asserted only for ground states whose squared staggered order parameter
`⟨Φ, (Ô_L^{(3)}/L^d)² Φ⟩ = ⟨Φ, Ô² Φ⟩ / (⟨Φ,Φ⟩ · (L^d)²)` is bounded below by `q₀` (the LRO
hypothesis, eq. (4.1.7)).  In one dimension there is no such ground state (Corollary 4.3,
`no_long_range_order_1d`), so the statement is vacuous there — exactly as in Tasaki.
Tasaki sketches the reflection-positivity / infinite-volume proof (§4.2.2); recorded here as a
faithful, sound documented axiom over the concrete torus family.

The body is factored as the predicate `IsAndersonTowerConstants d N q₀ C₁ C₂` (positivity of the
constants together with the per-torus tower bound), so that Theorem 4.8 can assert the *same*
constants `C₁`, `C₂`. -/
def IsAndersonTowerConstants (d N : ℕ) (q₀ C₁ C₂ : ℝ) : Prop :=
  0 < C₁ ∧ 0 < C₂ ∧
    ∀ (L : ℕ) [NeZero L], 2 ≤ L → Even L →
      ∀ (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℂ) (M : ℤ),
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Φ = E₀ • Φ →
        (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
          (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) →
        Φ ≠ 0 →
        q₀ ≤ (star Φ ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
            staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ)).re /
            ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2) →
        (M.natAbs : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
        towerState (torusParitySublattice d L) N M Φ ≠ 0 →
        (star (towerState (torusParitySublattice d L) N M Φ) ⬝ᵥ
            (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
              (towerState (torusParitySublattice d L) N M Φ)).re /
          (star (towerState (torusParitySublattice d L) N M Φ) ⬝ᵥ
            towerState (torusParitySublattice d L) N M Φ).re ≤
        E₀.re + C₂ * (M : ℝ) ^ 2 / (L : ℝ) ^ d

axiom tower_lowLying_energy_bound (d N : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ : ℝ, IsAndersonTowerConstants d N q₀ C₁ C₂

/-- **Tasaki Corollary 4.7 (the tower of low-lying energy eigenstates), AXIOM.**  Exactly as
Theorem 3.1 turns a low-lying trial state into a low-lying energy eigenstate, Theorem 4.6 yields,
for each nonzero magnetization `M ≠ 0`, an energy eigenstate `Ψ_M` in the `Ŝ_tot^{(3)}` sector `M`
(eq. (4.2.7)): `E_GS < E_M ≤ E_GS + C₂ M² / L^d` (the strict gap is the excitation; `M = 0` is the
ground state itself, excluded).

Here the ground state `Φ` lies in a definite magnetization sector (`totalSpinSOp3 Φ = μ₀ • Φ`); the
tower raises/lowers the magnetization by `M`, so `Ψ_M` lies in the sector `μ₀ + M`
(`totalSpinSOp3 Ψ = (μ₀ + M) • Ψ`).  Distinct `M` give distinct (orthogonal) sectors, so this
exhibits `O(L^{d/2})` distinct low-lying energy eigenstates — the rigorous Anderson tower.  The
bound is conditional on long-range order (the same `q₀` premise as Theorem 4.6), hence vacuous in
one dimension by Corollary 4.3.  Recorded as a faithful, sound documented axiom over the torus. -/
axiom tower_lowLying_eigenstates (d N : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (L : ℕ) [NeZero L], 2 ≤ L → Even L →
        ∀ (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ μ₀ : ℂ) (M : ℤ),
          (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Φ = E₀ • Φ →
          (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) →
          Φ ≠ 0 →
          (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = μ₀ • Φ →
          q₀ ≤ (star Φ ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
              staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ)).re /
              ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2) →
          M ≠ 0 →
          (M.natAbs : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
          towerState (torusParitySublattice d L) N M Φ ≠ 0 →
          ∃ (Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E_M : ℂ),
            Ψ ≠ 0 ∧
            (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E_M • Ψ ∧
            E₀.re < E_M.re ∧ E_M.re ≤ E₀.re + C₂ * (M : ℝ) ^ 2 / (L : ℝ) ^ d ∧
            (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Ψ = (μ₀ + (M : ℂ)) • Ψ

/-- The Tanaka Theorem 4.8 energy bound for fixed constants `C₁`, `C₂` (the body of Theorem 4.8,
factored so that the axiom can assert the *same* constants as Theorem 4.6).  For each `M(L) > 0`
with `M + 1 ≤ C₁ L^{d/2}`, on every even-side torus the Tanaka symmetry-breaking state
`Ξ_{(1,0,0)} = tanakaSSBState A N M Φ` obeys the Rayleigh-ratio bound (eq. (4.2.11)):
`⟨Ξ, Ĥ Ξ⟩ / ⟨Ξ, Ξ⟩ ≤ E_GS + C₂ {M+1}² / L^d`.

The two tower terms and the state itself are required to have strictly positive squared norm
(`vecNormSqRe > 0`), the well-definedness condition for `unitNormalize` (the Tanaka state is built
by normalizing each term separately).  Conditional on long-range order (the same `q₀` premise as
Theorem 4.6), hence vacuous in one dimension by Corollary 4.3. -/
def IsTanakaSSBConstants (d N : ℕ) (q₀ C₁ C₂ : ℝ) : Prop :=
  0 < C₁ ∧ 0 < C₂ ∧
    ∀ (L : ℕ) [NeZero L], 2 ≤ L → Even L →
      ∀ (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℂ) (M : ℕ),
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Φ = E₀ • Φ →
        (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
          (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) →
        Φ ≠ 0 →
        q₀ ≤ (star Φ ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
            staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ)).re /
            ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2) →
        0 < M →
        ((M : ℝ) + 1) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
        0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ) →
        0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ) →
        0 < vecNormSqRe (tanakaSSBState (torusParitySublattice d L) N M Φ) →
        (star (tanakaSSBState (torusParitySublattice d L) N M Φ) ⬝ᵥ
            (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
              (tanakaSSBState (torusParitySublattice d L) N M Φ)).re /
          (star (tanakaSSBState (torusParitySublattice d L) N M Φ) ⬝ᵥ
            tanakaSSBState (torusParitySublattice d L) N M Φ).re ≤
        E₀.re + C₂ * ((M : ℝ) + 1) ^ 2 / (L : ℝ) ^ d

/-- **Tasaki Theorem 4.8 (the Tanaka symmetry-breaking state is low-lying), AXIOM.**  With the
*same* constants `C₁`, `C₂` as Theorem 4.6 (`IsAndersonTowerConstants`), the Tanaka state `Ξ`
(eq. (4.2.10)) — a candidate physical "ground state" with full symmetry breaking — is itself a
low-lying state (eq. (4.2.11), `IsTanakaSSBConstants`):
`⟨Ξ_{(1,0,0)}| Ĥ |Ξ_{(1,0,0)}⟩ / ⟨Ξ_{(1,0,0)}, Ξ_{(1,0,0)}⟩ ≤ E_GS + C₂ {M(L)+1}² / L^d`,
for any increasing `M = M(L) > 0` with `M + 1 ≤ C₁ L^{d/2}`.

Asserting both predicates with one pair `(C₁, C₂)` formalizes Tasaki's "with the same constants as
in Theorem 4.6".  Conditional on long-range order, hence vacuous in one dimension by Corollary 4.3.
Tasaki sketches the proof (§4.2.2, following Tanaka [62]); recorded here as a faithful, sound
documented axiom over the torus family. -/
axiom tanakaSSB_lowLying_energy_bound (d N : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ : ℝ, IsAndersonTowerConstants d N q₀ C₁ C₂ ∧ IsTanakaSSBConstants d N q₀ C₁ C₂

open Filter in
/-- The Theorem 4.9 full-symmetry-breaking statement for fixed constants `C₁` and order parameter
`mStar`.  For a slowly diverging sequence `M(L)` (`Tendsto M atTop atTop`, with `M(L) + 1 ≤
C₁ L^{d/2}`), the Tanaka state `Ξ_{(1,0,0)}` realizes full `SU(2)` symmetry breaking in the
direction (eqs. (4.2.12)–(4.2.15)):
* `lim_L ⟨Ξ| Ô_L^{(1)}/L^d |Ξ⟩ = mStar`                 (4.2.12),
* `lim_L ⟨Ξ| (Ô_L^{(1)}/L^d)² |Ξ⟩ = mStar²`             (4.2.13),
* `⟨Ξ| Ô_L^{(α)}/L^d |Ξ⟩ = 0` for `α = 2, 3`, all `L`   (4.2.14),
* `lim_L ⟨Ξ| (Ô_L^{(α)}/L^d)² |Ξ⟩ = 0` for `α = 2, 3`   (4.2.15).

All expectations are in scale-invariant Rayleigh-ratio form (`expectationRatioRe`), as `Ξ` is not
proven unit-normalized in Lean.  The ground state family `Φ` (energies `E₀`) is given, with the
minimizer / long-range-order conditions holding *eventually* (for all sufficiently large even `L`).
The theorem then asserts the existence of a *sufficiently slowly diverging* sequence `M(L)`
(`Tendsto M atTop atTop`, with the growth bound `M L + 1 ≤ C₁ L^{d/2}` and positive squared norms of
the Tanaka terms/state holding eventually) — Tasaki's proof produces such an `M`, not every
diverging one (Lemma 4.16 gives no concrete choice), so the statement is existential in `M`.  For
that `M`, the order-operator-density expectations obey the symmetry-breaking relations.

Per Tasaki footnote 21, the rigorous forms of (4.2.12)/(4.2.13) are `liminf`, so we state the sound
lower bounds `liminf_L ⟨Ô_L^{(1)}/L^d⟩ ≥ mStar` and `liminf_L ⟨(Ô_L^{(1)}/L^d)²⟩ ≥ mStar²` (i.e.
eventually `> mStar − ε` / `> mStar² − ε`); the matching upper bounds follow from `mStar` being the
*maximal* density (eq. (4.2.9)) and are not separately encoded.  The order parameter `mStar > 0` is
an existential real, not the double limit `lim_k lim_L`. -/
def IsTanakaFullSSBConstants (d N : ℕ) (q₀ C₁ mStar : ℝ) : Prop :=
  0 < C₁ ∧ 0 < mStar ∧
    ∀ (Φ : (L : ℕ) → (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℕ → ℂ),
      -- the ground-state / minimizer / LRO conditions hold *eventually* for the given family
      (∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec (Φ L) = E₀ L • Φ L ∧
        (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
          (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ → (E₀ L).re ≤ E.re) ∧
        Φ L ≠ 0 ∧
        q₀ ≤ (star (Φ L) ⬝ᵥ ((staggeredOrderOpS (torusParitySublattice d L) N *
            staggeredOrderOpS (torusParitySublattice d L) N).mulVec (Φ L))).re /
            ((star (Φ L) ⬝ᵥ Φ L).re * ((L : ℝ) ^ d) ^ 2)) →
      -- there exists a sufficiently slowly diverging M(L) for which the SSB relations hold
      ∃ M : ℕ → ℕ, Tendsto M atTop atTop ∧
        (∃ L₂ : ℕ, ∀ (L : ℕ) [NeZero L], L₂ ≤ L → 2 ≤ L → Even L →
          0 < M L ∧ ((M L : ℝ) + 1) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) ∧
          0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M L) (Φ L)) ∧
          0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M L + 1) (Φ L)) ∧
          0 < vecNormSqRe (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L))) ∧
        -- (4.2.12) liminf ≥ mStar
        (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
          mStar - ε < tanakaOrderMean1 d L N (M L) (Φ L)) ∧
        -- (4.2.13) liminf ≥ mStar²
        (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
          mStar ^ 2 - ε < tanakaOrderSecond1 d L N (M L) (Φ L)) ∧
        -- (4.2.14) the orthogonal moments vanish (eventually, exactly)
        (∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
          tanakaOrderMean2 d L N (M L) (Φ L) = 0 ∧ tanakaOrderMean3 d L N (M L) (Φ L) = 0) ∧
        -- (4.2.15) the orthogonal density fluctuations vanish
        (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
          |tanakaOrderSecond2 d L N (M L) (Φ L)| < ε ∧ |tanakaOrderSecond3 d L N (M L) (Φ L)| < ε)

/-- **Tasaki Theorem 4.9 (the Tanaka state exhibits full symmetry breaking), AXIOM.**  With the same
constants `C₁`, `C₂` as Theorem 4.6 and an order parameter `mStar > 0`, the Tanaka state
`|Ξ_{(1,0,0)}⟩` realizes full `SU(2)` symmetry breaking in the `(1,0,0)` direction (eqs.
(4.2.12)–(4.2.15)): for a *sufficiently slowly diverging* `M(L)` (existential, as Tasaki's proof
produces one — not every diverging sequence), the staggered moment per site has `liminf ≥ mStar`
along axis `1`, the squared moment `liminf ≥ mStar²` (the `liminf` forms per footnote 21), while
along axes `2, 3` both vanish — so the order-operator density behaves as a classical vector of
magnitude `mStar` pointing in `(1,0,0)`, with vanishing fluctuation.

The order parameter `mStar` is recorded as an existential real (`> 0`); its identity with the double
limit (4.2.9) and the inequality `mStar ≥ √(3 q₀)` (Theorem 4.11) are kept separate.  Conditional
on long-range order (same `q₀` premise as Theorem 4.6), hence vacuous in d=1 by Corollary 4.3.
Tasaki gives the complete proof (§4.2.2, following Tanaka [62]); recorded here as a faithful, sound
documented axiom over the torus family. -/
axiom tanakaSSB_full_symmetry_breaking (d N : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ mStar : ℝ, IsAndersonTowerConstants d N q₀ C₁ C₂ ∧
      IsTanakaSSBConstants d N q₀ C₁ C₂ ∧ IsTanakaFullSSBConstants d N q₀ C₁ mStar

end LatticeSystem.Quantum
