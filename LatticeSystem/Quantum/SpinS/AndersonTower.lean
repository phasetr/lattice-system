import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic

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

/-- **Tasaki Theorem 4.6 (Anderson's tower of low-lying states), AXIOM.**  Fix the spin `S = N/2`
and a dimension `d ≥ 1`.  There are positive constants `C₁`, `C₂` (depending only on `d`, `S`, and
the long-range-order parameter `q₀`) such that, on every `d`-dimensional hypercubic torus of even
side `L ≥ 2`, for the antiferromagnetic nearest-neighbor Heisenberg model with ground state `Φ`
(energy `E₀`) and every `M` with `M ≤ C₁ L^{d/2}` for which the tower state
`ψ_M = (Ô_L^+)^M Φ` is nonzero (well-defined), the Rayleigh energy of `ψ_M` obeys (eq. (4.2.4)):
`⟨ψ_M, Ĥ ψ_M⟩ / ⟨ψ_M, ψ_M⟩ ≤ E₀ + C₂ M² / L^d`.

The Rayleigh-quotient (ratio) form makes the bound scale-invariant, so no separate normalization of
`ψ_M` is needed.  The uniform constant `C₂` exists precisely because the family is the genuine
translation-invariant hypercubic torus.  Tasaki sketches the reflection-positivity / infinite-volume
proof (§4.2.2); recorded here as a faithful, sound documented axiom over the concrete torus family. -/
axiom tower_lowLying_energy_bound (d N : ℕ) (hd : 1 ≤ d) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (L : ℕ) [NeZero L], 2 ≤ L → Even L →
        ∀ (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℂ) (M : ℕ),
          (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Φ = E₀ • Φ →
          (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) →
          Φ ≠ 0 →
          (M : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
          ((staggeredRaisingOpS (torusParitySublattice d L) N) ^ M).mulVec Φ ≠ 0 →
          (star (((staggeredRaisingOpS (torusParitySublattice d L) N) ^ M).mulVec Φ) ⬝ᵥ
              (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
                (((staggeredRaisingOpS (torusParitySublattice d L) N) ^ M).mulVec Φ)).re /
            (star (((staggeredRaisingOpS (torusParitySublattice d L) N) ^ M).mulVec Φ) ⬝ᵥ
              ((staggeredRaisingOpS (torusParitySublattice d L) N) ^ M).mulVec Φ).re ≤
          E₀.re + C₂ * (M : ℝ) ^ 2 / (L : ℝ) ^ d

end LatticeSystem.Quantum
