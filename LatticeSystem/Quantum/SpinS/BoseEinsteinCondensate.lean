import LatticeSystem.Quantum.SpinS.HeisenbergEquilibrium
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenberg

/-!
# Tasaki §5.1–§5.2: Bose–Einstein condensation of hard-core bosons and off-diagonal long-range
order (Theorem 5.1)

Tasaki Chapter 5 studies **Bose–Einstein condensation (BEC)** of bosons on the `d`-dimensional
hypercubic lattice.  In the limit of infinitely strong on-site repulsion (`u ↑ ∞`) the bosonic
Hubbard model (5.1.3) reduces to the model of **hard-core bosons** with the hopping Hamiltonian
`Ĥ = P̂_hc (−Σ_{⟨x,y⟩}(â_x† â_y + â_y† â_x))` (5.1.4) on the `N`-particle Hilbert space.  This model
is **equivalent to the spin-`1/2` XY model** (§5.1, eq. (5.1.5))
`Ĥ_XY = Σ_{⟨x,y⟩}(Ŝ_x^{(1)} Ŝ_y^{(1)} + Ŝ_x^{(2)} Ŝ_y^{(2)})`,
under the identification (5.1.6) `â_x† ↔ (−1)^x Ŝ_x^+`, `â_x ↔ (−1)^x Ŝ_x^−`, with the dictionary
(5.1.7) `2 Ĥ_XY ↔ Ĥ`, `Ŝ_x^{(3)} + 1/2 ↔ n̂_x`, `Ŝ_tot^{(3)} + L^d/2 ↔ N̂`.  Half filling
`ρ = N/L^d = 1/2` corresponds to the `Ŝ_tot^{(3)} = 0` sector, where the XY ground state lives
(Theorem 2.4).

The bosonic order operators `Ô_L^± = Σ_x â_x†`, `Σ_x â_x` (5.2.2) correspond to the staggered spin
order operators `Σ_x (−1)^x Ŝ_x^±`; their self-adjoint combinations `Ô_L^{(1)} = (Ô_L^+ + Ô_L^−)/2`,
`Ô_L^{(2)} = (Ô_L^+ − Ô_L^−)/(2i)` (5.2.4) are exactly the staggered XY-plane order operators
`staggeredOrderOp1S`, `staggeredOrderOp2S` on the parity sublattice.  **Off-diagonal long-range
order (ODLRO)** — the hallmark of BEC, `⟨Φ_GS| â_x† â_y |Φ_GS⟩ → const > 0` (5.2.1) — is then the
statement (5.2.5) `⟨Φ_GS| (Ô_L^{(α)})² / L^d |Φ_GS⟩ ≥ q₀ > 0` for `α = 1, 2`.

**Theorem 5.1**: for `d ≥ 2` and half filling `ρ = 1/2`, ODLRO holds with a constant `q₀ > 0`
depending only on `d`.  This is the BEC counterpart of the Dyson–Lieb–Simon Néel order; it was
proved by Kennedy–Lieb–Shastry and by Kubo–Kishi via reflection positivity.  Being an
infinite-volume result, it is recorded here as a documented axiom on the spin (XY) side.  (The
ground state itself exhibits *no* SSB, `⟨Ô_L^{(α)}/L^d⟩ = 0`, since it has a fixed particle number —
LRO without SSB, eq. (5.2.8).)

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.1–§5.2, Theorem 5.1, eqs. (5.1.1)–(5.2.5), pp. 135–139.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The **spin-`1/2` XY Hamiltonian** on the `d`-dimensional hypercubic torus (eq. (5.1.5)):
`Ĥ_XY = Σ_{x,y} J_{xy} (Ŝ_x^{(1)} Ŝ_y^{(1)} + Ŝ_x^{(2)} Ŝ_y^{(2)})`, realized as the XXZ Hamiltonian
at anisotropy `λ = 0` and single-ion term `D = 0` with the nearest-neighbor coupling
`torusNNCoupling`.  This is the spin form of the hard-core boson hopping Hamiltonian `Ĥ` (5.1.4)
under the identification (5.1.6) (up to the positive factor `2` and the gauge sign, both of which
leave the ground states and
ODLRO invariant). -/
noncomputable def xyHamiltonianS (d L : ℕ) [NeZero L] :
    ManyBodyOpS (HypercubicTorus d L) 1 :=
  anisotropicHeisenbergS (torusNNCoupling d L) 0 0 1

/-- **Tasaki Theorem 5.1 (off-diagonal long-range order of hard-core bosons at half filling),
AXIOM.**  For the spin-`1/2` XY model (the `u ↑ ∞` hard-core boson model) on the `d`-dimensional
hypercubic torus with `d ≥ 2`, at half filling `ρ = 1/2` (the `Ŝ_tot^{(3)} = 0` sector), there is a
constant `q₀ > 0` depending only on `d` such that every ground state `Φ_GS` exhibits ODLRO
(eq. (5.2.5)): for the two XY-plane staggered order operators `Ô_L^{(α)}` (`α = 1, 2`, here
`α : Fin 3` with `α ≠ 2`),
`⟨Φ_GS| (Ô_L^{(α)})² Φ_GS⟩ / ⟨Φ_GS| Φ_GS⟩ / (L^d)² ≥ q₀`,
for all sufficiently large even `L`.  The squared order parameter is normalized by `(L^d)²` (the
operator `Ô_L^{(α)}/L^d` is squared, eqs. (5.2.3)/(5.2.5)), the intensive ODLRO density.

The ground state `Φ_GS` is a *given* per-`L` vector specified by the hypotheses (eigenvector of
`xyHamiltonianS` at the minimal real eigenvalue, nonzero, and in the half-filling sector
`Ŝ_tot^{(3)} Φ_GS = 0`); the bound holds for *every* such ground state.  Half filling
(`Ŝ_tot^{(3)} = 0`) is essential — it is the sector to which ODLRO/BEC corresponds (Theorem 2.4) —
and `Φ ≠ 0` makes the Rayleigh ratio well defined.  Proved by Kennedy–Lieb–Shastry and Kubo–Kishi
via the reflection-positivity method of Dyson–Lieb–Simon; recorded as a documented axiom. -/
axiom tasaki_5_1_xy_odlro_half_filling (d : ℕ) (hd : 2 ≤ d) :
    ∃ q₀ : ℝ, 0 < q₀ ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], Even L → L₀ ≤ L →
      ∀ (Φ : (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℂ), Φ ≠ 0 →
        (xyHamiltonianS d L).mulVec Φ = E₀ • Φ →
        (∀ (E : ℂ) (Ψ : (HypercubicTorus d L → Fin 2) → ℂ), Ψ ≠ 0 →
          (xyHamiltonianS d L).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) →
        (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0 →
        ∀ (α : Fin 3), α ≠ 2 →
          q₀ ≤ expectationRatioRe
            ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2

end LatticeSystem.Quantum
