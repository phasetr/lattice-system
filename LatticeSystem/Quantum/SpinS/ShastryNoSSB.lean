import LatticeSystem.Quantum.SpinS.DysonLiebSimon
import LatticeSystem.Quantum.SpinS.Heisenberg

/-!
# Tasaki §4.1: absence of symmetry breaking in one dimension (Theorem 4.2, Shastry)

For the one-dimensional spin-`S` antiferromagnetic Heisenberg model on a ring of `L` sites under a
staggered magnetic field (eq. (4.1.9)),
`Ĥ_h = Σ_x Ŝ_x · Ŝ_{x+1} − h Σ_x (−1)^x Ŝ_x^{(3)}` (periodic, `Ŝ_{L+1} = Ŝ_1`),
Shastry's theorem (Theorem 4.2) asserts that the staggered order parameter vanishes in the iterated
thermodynamic-then-zero-field limit (eq. (4.1.10)):
`lim_{h↓0} lim_{L↑∞} ⟨Φ_GS,h| Ô_L^{(3)}/L |Φ_GS,h⟩ = 0`,
so the model never exhibits spontaneous symmetry breaking even though the staggered field is
designed to enhance the staggered moment.

Tasaki does **not** prove Theorem 4.2 (the original argument of Shastry [58] is not stated as a
mathematical theorem; a rigorous formulation is in [63]).  We record it as a documented axiom,
stated faithfully and soundly over the concrete one-dimensional ring family: the order parameter is
normalized per site, the ground states are *normalized* energy-minimizing eigenvectors (so the bound
is scale-invariant), and the double limit is written in explicit `ε`–`δ` form (for every `ε > 0`
there is a field threshold `h₀`, and for each small field a size threshold `L₀`, beyond which the
per-site staggered moment is `< ε`).  The deep argument behind it (a thermodynamic / infinite-volume
statement) is deferred; infinite-volume systems are in scope (the project's central long-term goal).

This file defines the ring nearest-neighbor coupling, the staggered-field chain Hamiltonian, and
states Theorem 4.2.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, Theorem 4.2, eqs. (4.1.9)–(4.1.10), pp. 76–77 (Shastry [58]; cf. [63]).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {N : ℕ}

/-- The **directed nearest-neighbor coupling on the ring** `Fin L`: `J x y = 1` exactly when `y` is
the cyclic successor `x + 1 (mod L)` of `x`, and `0` otherwise.  Summed against `Ŝ_x · Ŝ_y` this
reproduces the periodic chain interaction `Σ_x Ŝ_x · Ŝ_{x+1}` (with `Ŝ_{L+1} = Ŝ_1`). -/
def ringCoupling (L : ℕ) (x y : Fin L) : ℂ :=
  if y.val = (x.val + 1) % L then 1 else 0

/-- The **staggered sublattice sign** on the ring `Fin L`: `A x = true` on even sites and `false` on
odd sites, so the associated sublattice sign is `ε_x = (−1)^x`.  Used with `staggeredOrderOpS` it
gives the staggered order operator `Ô_L^{(3)} = Σ_x (−1)^x Ŝ_x^{(3)}`. -/
def ringStaggeredSublattice (L : ℕ) (x : Fin L) : Bool := x.val % 2 = 0

/-- The **one-dimensional staggered-field antiferromagnetic Heisenberg Hamiltonian** on a ring of
`L` sites (eq. (4.1.9)): `Ĥ_h = Σ_x Ŝ_x · Ŝ_{x+1} − h · Ô_L^{(3)}`, with `Ô_L^{(3)}` the staggered
order operator.  The staggered field `−h (−1)^x Ŝ_x^{(3)}` is designed to trigger possible symmetry
breaking. -/
noncomputable def staggeredFieldChainHamiltonianS (L : ℕ) (h : ℝ) (N : ℕ) :
    ManyBodyOpS (Fin L) N :=
  heisenbergHamiltonianS (ringCoupling L) N
    - (h : ℂ) • staggeredOrderOpS (ringStaggeredSublattice L) N

/-- **Tasaki Theorem 4.2 (Shastry no-SSB in 1D), DOCUMENTED AXIOM.**
Tasaki §4.1 footnote 3 (p. 76) explicitly states "We do not prove Theorem 4.2 in
the present book" and refers to Shastry [58] argument (J. Phys. A 25: L249, 1992)
and its rigorous formulation in Tanaka–Takeda–Idogaki [63] (J. Magn. Magn. Mater.
272–276: 908, 2004). Thus Thm 4.2 is a **cite-only documented axiom**.

**Statement (finite-dimensional, iterated limit form)**: For 1D spin-`S`
antiferromagnetic Heisenberg ring under staggered field `Ĥ_h = Σ_x Ŝ_x · Ŝ_{x+1}
− h · Ô_L^{(3)}` (eq. (4.1.9)), the per-site staggered order parameter of any
*normalized* ground state vanishes in the iterated limit `lim_{h↓0} lim_{L↑∞}`
(eq. (4.1.10)): for every `ε > 0` there is a field threshold `h₀ > 0` such that
for each field `0 < h < h₀` there is a size threshold `L₀` beyond which every
normalized ground state `Φ` of `staggeredFieldChainHamiltonianS L h N` has
`|⟨Φ, Ô_L^{(3)} Φ⟩.re / L| < ε`.

Here a ground state is a normalized energy-minimizing eigenvector (`Φ ≠ 0`,
`star Φ ⬝ᵥ Φ = 1`, `Ĥ_h Φ = E₀ • Φ` with `E₀.re` minimal over eigenpairs);
normalization makes per-site bound scale-invariant. We record it as a faithful,
sound documented axiom over the concrete ring family (Tasaki does not prove it,
citing the original Shastry argument [58] and its rigorous formulation [63]).
The deep thermodynamic-limit / infinite-volume argument (Shastry–Tanaka–Takeda–
Idogaki) is documented-axiom material; the reflection-positivity infrastructure
project (#4777) formalizes supporting finite-dim RP layers for the Gibbs
decomposition, not a re-proof of Thm 4.2 itself. -/
axiom shastry_no_symmetry_breaking_1d (N : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ h : ℝ, 0 < h → h < h₀ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
        ∀ Φ : (Fin L → Fin (N + 1)) → ℂ,
          star Φ ⬝ᵥ Φ = 1 →
          (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L h N).mulVec Φ = E₀ • Φ ∧
            (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
              (staggeredFieldChainHamiltonianS L h N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
            Φ ≠ 0) →
          |(star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re / (L : ℝ)| < ε

end LatticeSystem.Quantum
