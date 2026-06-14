import LatticeSystem.Quantum.SpinS.HeisenbergEquilibrium
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenberg

/-!
# Tasaki §5.1–§5.3: Bose–Einstein condensation of hard-core bosons — off-diagonal long-range order
and low-lying tower states (Theorems 5.1, 5.2)

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

/-! ## Theorem 5.2: low-lying tower states of hard-core bosons -/

/-- The **chemical-potential XY Hamiltonian** `Ĥ_μ = Ĥ_XY − μ N̂` (eq. (5.3.2)) on the
`d`-dimensional torus, in spin form: `N̂ ↔ Ŝ_tot^{(3)} + L^d/2` (5.1.7), so up to the constant
`μ L^d/2` (which cancels in all energy *differences*) the chemical-potential term is
`−μ Ŝ_tot^{(3)}`.  Adjusting `μ` selects the particle density `ρ = N/L^d` of the ground state; half
filling is `μ = 0`. -/
noncomputable def xyChemicalPotentialHamiltonianS (d L : ℕ) [NeZero L] (μ : ℝ) :
    ManyBodyOpS (HypercubicTorus d L) 1 :=
  xyHamiltonianS d L - (μ : ℂ) • totalSpinSOp3 (HypercubicTorus d L) 1

/-- **The BEC tower constants predicate** (Tasaki Theorem 5.2, eq. (5.3.4)).  `IsBECTowerConstants d
q₀ C₁ C₂` asserts that `C₁, C₂ > 0` and, for every even torus side `L ≥ 2`, every chemical potential
`μ`, and every ground state `Φ_GS` of the chemical-potential XY Hamiltonian `Ĥ_μ`
(eigenvector at the minimal real eigenvalue `E₀`, nonzero) that exhibits ODLRO with parameter `q₀`
(the half-filling/XY-plane order parameters `⟨(Ô_L^{(α)})²⟩/(⟨Φ,Φ⟩ (L^d)²) ≥ q₀` for `α = 1, 2`,
as in Theorem 5.1), the tower state `Γ_M = (Ô_L^{sgn M})^{|M|} Φ_GS` (for `|M| ≤ C₁ L^{d/2}`,
nonvanishing) is low-lying with the **cubic** energy increment (eq. (5.3.4))
`⟨Γ_M, Ĥ_μ Γ_M⟩ / ⟨Γ_M, Γ_M⟩ ≤ E₀ + C₂ |M|³ / L^d`.
(The hard-core projection `P̂_hc` is the identity in the spin-`1/2` formulation.) -/
def IsBECTowerConstants (d : ℕ) (q₀ C₁ C₂ : ℝ) : Prop :=
  0 < C₁ ∧ 0 < C₂ ∧
    ∀ (L : ℕ) [NeZero L], 2 ≤ L → Even L →
      ∀ (μ : ℝ) (Φ : (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℂ) (M : ℤ),
        (xyChemicalPotentialHamiltonianS d L μ).mulVec Φ = E₀ • Φ →
        (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin 2) → ℂ, Ψ ≠ 0 →
          (xyChemicalPotentialHamiltonianS d L μ).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) →
        Φ ≠ 0 →
        (∀ α : Fin 3, α ≠ 2 →
          q₀ ≤ expectationRatioRe
            ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2) →
        (M.natAbs : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
        towerState (torusParitySublattice d L) 1 M Φ ≠ 0 →
        expectationRatioRe (xyChemicalPotentialHamiltonianS d L μ)
            (towerState (torusParitySublattice d L) 1 M Φ) ≤
          E₀.re + C₂ * (M.natAbs : ℝ) ^ 3 / (L : ℝ) ^ d

/-- **Tasaki Theorem 5.2 (low-lying tower states of hard-core bosons), AXIOM.**  Suppose the ground
state `Φ_GS` of the chemical-potential XY Hamiltonian `Ĥ_μ` (5.3.2) exhibits ODLRO with some
constant `q₀ > 0` (Theorem 5.1, eq. (5.2.5)).  Then there are constants `C₁, C₂ > 0` — depending
only on `d`,
the density, and `q₀` — such that the bosonic tower states `Γ_M` are low-lying with the cubic energy
bound `⟨Γ_M, Ĥ_μ Γ_M⟩ ≤ ⟨Φ_GS, Ĥ_μ Φ_GS⟩ + C₂ |M|³ / L^d` for `|M| ≤ C₁ L^{d/2}` (eq. (5.3.4)).

This is the BEC counterpart of the Anderson-tower Theorem 4.6; the construction and the constants
are bundled into `IsBECTowerConstants` (the energy increment is **cubic** in `|M|`, not quadratic as
in
Theorem 4.6).  Like Theorem 4.6 the bound is conditional on ODLRO (`q₀ > 0`), so it is vacuous where
ODLRO is absent.  Proved in Koma–Tasaki [21]; recorded as a documented axiom. -/
axiom tasaki_5_2_bec_tower (d : ℕ) (hd : 2 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ : ℝ, IsBECTowerConstants d q₀ C₁ C₂

end LatticeSystem.Quantum
