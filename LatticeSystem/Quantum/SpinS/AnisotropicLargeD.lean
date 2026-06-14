import LatticeSystem.Quantum.SpinS.AKLTStability

/-!
# Tasaki §8.1.1: the large-`D` phase of the anisotropic `S = 1` chain (Theorem 8.1)

The **Haldane phase** is studied through the anisotropic `S = 1` antiferromagnetic Hamiltonian with
a
crystal-field (single-ion) anisotropy `D ≥ 0` (eq. (8.1.1))
`Ĥ_D = Σ_x [Ŝ_x·Ŝ_{x+1} + D (Ŝ_x^{(3)})²]`  (periodic boundary, `L` even).
At `D = 0` this is the `S = 1` Heisenberg chain (Haldane gap `≈ 0.41`); as `D` grows the gap closes
at
a critical `D_c ≈ 1` and reopens, separating the **Haldane phase** (`0 ≤ D ≤ D_c`) from the
**large-`D` phase** (`D > D_c`).  Both phases are unique, disordered and gapped with no broken
symmetry — a *topological* phase transition (no order parameter distinguishes them).

For large `D`, the model is a small perturbation of the trivial Hamiltonian `D Σ_x (Ŝ_x^{(3)})²`,
whose unique ground state has every spin in the `Ŝ^{(3)} = 0` state with gap `D`.  Rigorous cluster
expansion then gives:

**Theorem 8.1**: there is a constant `D₀ > 0` such that for every `D ≥ D₀` the gap `ΔE(D)` of `Ĥ_D`
is at least a positive `L`-independent `ΔE₀(D) > 0`, the ground-state spin correlations
`⟨Φ_GS| Ŝ_x^{(α)} Ŝ_y^{(α)} |Φ_GS⟩` decay exponentially in `|x − y|`, and the `L ↑ ∞` ground state
is
unique and gapped.

The anisotropic Hamiltonian and the spin-component selector are *defined concretely*.  Theorem 8.1,
whose proof is rigorous perturbation theory (cluster expansion) valid for large `D` (the book notes
`D₀ ≈ 28` suffices, while the phase actually extends to `D_c ≈ 1`), is recorded as a documented
axiom.  The correlation is the raw two-point function: in the disordered, symmetric large-`D` ground
state the one-point functions vanish, so raw and connected correlations coincide.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.1.1, Theorem 8.1, eqs. (8.1.1)–(8.1.3), pp. 226–228; T. Kennedy, H. Tasaki, Commun. Math.
Phys. **147**, 431 (1992).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- The **anisotropic `S = 1` antiferromagnetic chain Hamiltonian** with crystal-field anisotropy
`D` (eq. (8.1.1)): `Ĥ_D = Σ_x [Ŝ_x·Ŝ_{x+1} + D (Ŝ_x^{(3)})²]` on the periodic ring `Fin L`, the
nearest-neighbour Heisenberg term plus the single-ion `D (Ŝ^{(3)})²` term. -/
noncomputable def anisotropicChainHamiltonianS (L : ℕ) (D : ℝ) : ManyBodyOpS (Fin L) 2 :=
  heisenbergHamiltonianS (ringCoupling L) 2 +
    (D : ℂ) • ∑ x : Fin L, spinSSiteOp3 x 2 * spinSSiteOp3 x 2

/-- The site-`x` spin component `Ŝ_x^{(α)}` selected by `α : Fin 3` (`0 ↦ Ŝ^{(1)}`, `1 ↦ Ŝ^{(2)}`,
`2 ↦ Ŝ^{(3)}`), used to state the correlation decay for all three spin directions. -/
noncomputable def spinSSiteComponentS (α : Fin 3) (x : Fin L) : ManyBodyOpS (Fin L) 2 :=
  ![spinSSiteOp1 x 2, spinSSiteOp2 x 2, spinSSiteOp3 x 2] α

/-- **Tasaki Theorem 8.1 (large-`D` phase: gap and exponential clustering), AXIOM.**  There is a
threshold `D₀ > 0` such that for every anisotropy `D ≥ D₀` there are positive constants `ΔE₀, C, ξ`
— depending on `D` but **independent of the chain length `L`** — with the following property: for
every even `L ≥ 2`, the anisotropic chain `Ĥ_D` has a **unique ground state** `Φ`
(`IsUniqueChainGroundState`), a **gap** above it of at least `ΔE₀`
(`∃ gap ≥ ΔE₀`, `IsPositiveSpectralGap`), and **exponentially decaying** ground-state spin
correlations in every direction: `|⟨Ŝ_x^{(α)} Ŝ_y^{(α)}⟩| ≤ C e^{−d(x,y)/ξ}` for all `α` and all
sites (`d` the ring distance).  The large-`D` phase is thus a unique, disordered, gapped phase.
Proved by rigorous perturbation theory (cluster expansion) for large `D`; recorded as a documented
axiom. -/
axiom tasaki_theorem_8_1 :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ∃ ΔE₀ C ξ : ℝ, 0 < ΔE₀ ∧ 0 < C ∧ 0 < ξ ∧
        ∀ L : ℕ, Even L → 2 ≤ L →
          ∃ (E : ℝ) (Φ : (Fin L → Fin 3) → ℂ),
            IsUniqueChainGroundState (anisotropicChainHamiltonianS L D) E Φ ∧
            (∃ gap : ℝ, ΔE₀ ≤ gap ∧
              IsPositiveSpectralGap (anisotropicChainHamiltonianS L D) gap) ∧
            ∀ (α : Fin 3) (x y : Fin L),
              |expectationRatioRe (spinSSiteComponentS α x * spinSSiteComponentS α y) Φ| ≤
                C * Real.exp (-(ringDist L x y : ℝ) / ξ)

end LatticeSystem.Quantum
