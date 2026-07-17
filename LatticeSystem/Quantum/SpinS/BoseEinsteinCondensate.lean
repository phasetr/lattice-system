import LatticeSystem.Quantum.SpinS.HeisenbergEquilibrium
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenberg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tasaki §5.1–§5.5: Bose–Einstein condensation of hard-core bosons — off-diagonal long-range order,
low-lying tower states, U(1) symmetry breaking, and coupled condensates
(Theorems 5.1, 5.2, 5.3, 5.4)

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
proved by Kennedy–Lieb–Shastry and by Kubo–Kishi via reflection positivity.  The statement recorded
here is **uniform-in-`L` finite-dimensional** — the same pattern as the discharged Theorems
4.6/4.8/4.9/4.11 — *not* a true infinite-volume claim.  It is a documented axiom because the
`d`-dimensional reflection-positivity / infrared-bound proof technique
(Dyson–Lieb–Simon / Kennedy–Lieb–Shastry / Kubo–Kishi) is intractable at this project's scale (the
existing reflection-positivity infrastructure is one-dimensional-ring-only), *not* because the
subject is infinite-volume.  Rectification condition: should a `d`-dimensional RP/IR-bound
infrastructure ever be built, Theorem 5.1 returns to a prove-target.  (The ground state itself
exhibits *no* SSB, `⟨Ô_L^{(α)}/L^d⟩ = 0`, since it has a fixed particle number — LRO without SSB,
eq. (5.2.8).)

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
via the reflection-positivity method of Dyson–Lieb–Simon.  Despite invoking `d`-dimensional
reflection positivity, this statement is **uniform-in-`L` finite-dimensional** (like Theorems
4.6/4.8/4.9/4.11); it is a documented axiom because the `d`-dim RP/IR-bound proof technique is
intractable at project scale (the existing RP infrastructure is 1D-ring-only), *not* because the
subject is infinite-volume.  It returns to a prove-target if a `d`-dim RP/IR-bound infrastructure is
ever built. -/
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

/-- The **chemical-potential boson Hamiltonian** `Ĥ_μ = Ĥ − μ N̂` (eq. (5.3.2)) on the
`d`-dimensional torus, in spin form.  Per the dictionary (5.1.7) the hard-core boson Hamiltonian is
`Ĥ = 2 Ĥ_XY` and
`N̂ ↔ Ŝ_tot^{(3)} + L^d/2`, so `Ĥ_μ = 2 Ĥ_XY − μ Ŝ_tot^{(3)}` up to the additive constant `μ L^d/2`
(which cancels in all energy *differences*); the factor `2` on the XY term keeps the documented `μ`
equal to Tasaki's chemical potential, so adjusting `μ` selects the particle density `ρ = N/L^d` with
the textbook normalization (half filling is `μ = 0`). -/
noncomputable def xyChemicalPotentialHamiltonianS (d L : ℕ) [NeZero L] (μ : ℝ) :
    ManyBodyOpS (HypercubicTorus d L) 1 :=
  (2 : ℂ) • xyHamiltonianS d L - (μ : ℂ) • totalSpinSOp3 (HypercubicTorus d L) 1

/-- **The BEC tower constants predicate** (Tasaki Theorem 5.2, eq. (5.3.4)).  `IsBECTowerConstants d
μ q₀ C₁ C₂` asserts that `C₁, C₂ > 0` and, for the chemical potential `μ` (which selects the density
`ρ`, so the constants `C₁, C₂` depend on `μ`), every even torus side `L ≥ 2`, and every ground state
`Φ_GS` of the chemical-potential XY Hamiltonian `Ĥ_μ`
(eigenvector at the minimal real eigenvalue `E₀`, nonzero) that exhibits ODLRO with parameter `q₀`
(the half-filling/XY-plane order parameters `⟨(Ô_L^{(α)})²⟩/(⟨Φ,Φ⟩ (L^d)²) ≥ q₀` for `α = 1, 2`,
as in Theorem 5.1), the tower state `Γ_M = (Ô_L^{sgn M})^{|M|} Φ_GS` (for `|M| ≤ C₁ L^{d/2}`) is
**well-defined (nonvanishing) and** low-lying with the **cubic** energy increment (eq. (5.3.4)):
`towerState ≠ 0 ∧ ⟨Γ_M, Ĥ_μ Γ_M⟩ / ⟨Γ_M, Γ_M⟩ ≤ E₀ + C₂ |M|³ / L^d`.  Both the nonvanishing and the
energy bound are *conclusions* (faithful to Theorem 5.2, which asserts `Γ_M` is nonvanishing).
(The hard-core projection `P̂_hc` is the identity in the spin-`1/2` formulation.) -/
def IsBECTowerConstants (d : ℕ) (μ q₀ C₁ C₂ : ℝ) : Prop :=
  0 < C₁ ∧ 0 < C₂ ∧
    ∀ (L : ℕ) [NeZero L], 2 ≤ L → Even L →
      ∀ (Φ : (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℂ) (M : ℤ),
        (xyChemicalPotentialHamiltonianS d L μ).mulVec Φ = E₀ • Φ →
        (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin 2) → ℂ, Ψ ≠ 0 →
          (xyChemicalPotentialHamiltonianS d L μ).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) →
        Φ ≠ 0 →
        (∀ α : Fin 3, α ≠ 2 →
          q₀ ≤ expectationRatioRe
            ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2) →
        (M.natAbs : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
        towerState (torusParitySublattice d L) 1 M Φ ≠ 0 ∧
          expectationRatioRe (xyChemicalPotentialHamiltonianS d L μ)
              (towerState (torusParitySublattice d L) 1 M Φ) ≤
            E₀.re + C₂ * (M.natAbs : ℝ) ^ 3 / (L : ℝ) ^ d

/-- **The half-filling BEC tower constants predicate** (Tasaki Theorem 5.2, eq. (5.3.4), footnote 8,
p. 141).  `IsBECTowerConstantsHalfFilling d q₀ C₁ C₂` is the `μ = 0` (half-filling) kernel of
`IsBECTowerConstants`: it fixes the chemical potential to `μ = 0` (so the `Ĥ_μ = 2 Ĥ_XY` energy
carries no `−μ Ŝ_tot^{(3)}` term) and adds, as an inner premise conjunct, the half-filling sector
condition `Ŝ_tot^{(3)} Φ = 0` (the same sector hypothesis as Theorem 5.1
`tasaki_5_1_xy_odlro_half_filling`).  Under these hypotheses — `Φ_GS` a nonzero minimal-energy
eigenvector of `Ĥ_0 = 2 Ĥ_XY` in the `Ŝ_tot^{(3)} = 0` sector exhibiting the two XY-plane ODLRO
bounds (`α = 1, 2`) with parameter `q₀`, and `|M| ≤ C₁ L^{d/2}` — the tower state
`Γ_M = (Ô_L^{sgn M})^{|M|} Φ_GS` is **nonvanishing and** low-lying with the **cubic** energy
increment `towerState ≠ 0 ∧ ⟨Γ_M, Ĥ_0 Γ_M⟩ / ⟨Γ_M, Γ_M⟩ ≤ E₀ + C₂ |M|³ / L^d`.

Unlike the general-`μ` `IsBECTowerConstants` (kept as the faithful documented axiom
`tasaki_5_2_bec_tower`, whose general-`μ` bound rests on the Koma–Tasaki [21]
reflection-positivity/infrared machinery, intractable at project scale), this half-filling kernel is
discharged **axiom-free**: at `μ = 0` the variational numerator is the pure XY double commutator
(`xy_tower_numerator_bound`), so the Anderson-tower engine (Theorem 4.6) applies with the XY-plane
`p̂`-moment recursion in place of the `SU(2)` isotropy base.  The extra `Ŝ_tot^{(3)} Φ = 0` conjunct
is required because the reused denominator/numerator bricks all need the half-filling sector; a
general-`μ` ground state has `Ŝ_tot^{(3)} Φ = s₀ ≠ 0`, so this predicate is a genuinely stronger
statement (not `α`-equivalent to `IsBECTowerConstants`). -/
def IsBECTowerConstantsHalfFilling (d : ℕ) (q₀ C₁ C₂ : ℝ) : Prop :=
  0 < C₁ ∧ 0 < C₂ ∧
    ∀ (L : ℕ) [NeZero L], 2 ≤ L → Even L →
      ∀ (Φ : (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℂ) (M : ℤ),
        (xyChemicalPotentialHamiltonianS d L 0).mulVec Φ = E₀ • Φ →
        (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin 2) → ℂ, Ψ ≠ 0 →
          (xyChemicalPotentialHamiltonianS d L 0).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) →
        Φ ≠ 0 →
        (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0 →
        (∀ α : Fin 3, α ≠ 2 →
          q₀ ≤ expectationRatioRe
            ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2) →
        (M.natAbs : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
        towerState (torusParitySublattice d L) 1 M Φ ≠ 0 ∧
          expectationRatioRe (xyChemicalPotentialHamiltonianS d L 0)
              (towerState (torusParitySublattice d L) 1 M Φ) ≤
            E₀.re + C₂ * (M.natAbs : ℝ) ^ 3 / (L : ℝ) ^ d

/-- **Tasaki Theorem 5.2 (low-lying tower states of hard-core bosons), AXIOM.**  Suppose the ground
state `Φ_GS` of the chemical-potential XY Hamiltonian `Ĥ_μ` (5.3.2) exhibits ODLRO with some
constant `q₀ > 0` (Theorem 5.1, eq. (5.2.5)).  Then there are constants `C₁, C₂ > 0` — depending
only on `d`, the density (selected by `μ`), and `q₀` — such that the bosonic tower states `Γ_M` are
low-lying with the cubic energy
bound `⟨Γ_M, Ĥ_μ Γ_M⟩ ≤ ⟨Φ_GS, Ĥ_μ Φ_GS⟩ + C₂ |M|³ / L^d` for `|M| ≤ C₁ L^{d/2}` (eq. (5.3.4)).

This is the BEC counterpart of the Anderson-tower Theorem 4.6; the construction and the constants
are bundled into `IsBECTowerConstants` (the energy increment is **cubic** in `|M|`, not quadratic as
in
Theorem 4.6).  Like Theorem 4.6 the bound is conditional on ODLRO (`q₀ > 0`), so it is vacuous where
ODLRO is absent.  Proved in Koma–Tasaki [21]; recorded as a documented axiom.

**Half-filling kernel discharged.**  The `μ = 0` (half-filling) case is proved axiom-free as the
theorem `tasaki_5_2_bec_tower_half_filling` (predicate `IsBECTowerConstantsHalfFilling`,
`BoseEinsteinCondensateTower.lean`), whose `#print axioms` is `[propext, Classical.choice,
Quot.sound]` only.  The general-`μ` statement stays a documented axiom because at `μ ≠ 0` a ground
state has `Ŝ_tot^{(3)} Φ = s₀ ≠ 0`, so the reused variational bricks
(denominator/numerator/non-vanishing) — all requiring the half-filling `Ŝ_tot^{(3)} = 0` sector —
no longer close, and the general-`μ` bound rests on the Koma–Tasaki [21] `d`-dimensional
reflection-positivity/infrared machinery, the same RP-intractability exception as Theorem 5.1
(`tasaki_5_1_xy_odlro_half_filling`), intractable at project scale. -/
axiom tasaki_5_2_bec_tower (d : ℕ) (hd : 2 ≤ d) (μ q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ : ℝ, IsBECTowerConstants d μ q₀ C₁ C₂

/-! ## Theorem 5.3: the U(1) symmetry-breaking states of hard-core bosons -/

/-- The **complex Rayleigh expectation** `⟨w, O w⟩ / ⟨w, w⟩` of an operator `O` at a vector `w`.
Unlike `expectationRatioRe`, this keeps the full complex value, needed for the non-self-adjoint
order operators `Ô_L^±` (eq. (5.3.6)). -/
noncomputable def expectationRatioComplex {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℂ) (w : ι → ℂ) : ℂ :=
  (star w ⬝ᵥ O.mulVec w) / (star w ⬝ᵥ w)

/-- The **`U(1)` symmetry-breaking coherent state** `|Ξ_θ⟩` (eq. (5.3.5)): the phase-`θ`
superposition `Ξ_θ = (2 M_max + 1)^{-1/2} Σ_{M=−M_max}^{M_max} e^{−i M θ} Γ_M` of the normalized
tower states
`Γ_M = (Ô_L^{sgn M})^{|M|} Φ_GS / ‖·‖` (with `Γ_0 = Φ_GS`).  As `θ` varies, `Ξ_θ` is a `U(1)`
coherent state that fully breaks the phase symmetry of the hard-core boson model. -/
noncomputable def becCoherentState (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ) : (HypercubicTorus d L → Fin 2) → ℂ :=
  ((Real.sqrt (2 * (Mmax : ℝ) + 1) : ℝ) : ℂ)⁻¹ •
    ∑ M ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
      Complex.exp (-(M : ℝ) * θ * Complex.I) •
        unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)

/-- **Bilinear double-sum expansion of a coherent-state Rayleigh numerator** (Tasaki §5.3, the
algebraic core of eqs. (5.3.6)–(5.3.8), p. 141).  For any operator `O`, the sesquilinear form of the
`U(1)` coherent state `Ξ_θ` (`becCoherentState`, eq. (5.3.5)) expands over the tower window as
`⟨Ξ_θ, O Ξ_θ⟩ = (2 M_max + 1)^{-1} Σ_{M',M} conj(e^{−iM'θ}) e^{−iMθ} ⟨Γ_{M'}, O Γ_M⟩`, where
`Γ_M = unitNormalize (towerState … M Φ)`.  The prefactor `(2 M_max + 1)^{-1}` is `|c|²` for the real
normalization scalar `c = (√(2 M_max + 1))^{-1}` (self-conjugate as it is real).  This is the purely
algebraic step, prior to the sector orthogonality of the `Γ_M` (a later arc PR) collapsing the
double sum to its diagonal/adjacent band; taking `O = 1` gives the self inner product used for the
`‖Ξ_θ‖ = 1` normalization. -/
theorem becCoherentState_dotProduct_mulVec (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (O : Matrix (HypercubicTorus d L → Fin 2) (HypercubicTorus d L → Fin 2) ℂ) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ O.mulVec (becCoherentState d L θ Mmax Φ)
      = ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
        ∑ M' ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
          ∑ M ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
            (starRingEnd ℂ) (Complex.exp (-(M' : ℝ) * θ * Complex.I))
              * Complex.exp (-(M : ℝ) * θ * Complex.I)
              * (star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ))
                  ⬝ᵥ O.mulVec (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ))) := by
  have hs : (0 : ℝ) ≤ 2 * (Mmax : ℝ) + 1 := by positivity
  set c : ℂ := ((Real.sqrt (2 * (Mmax : ℝ) + 1) : ℝ) : ℂ)⁻¹ with hc
  have hcoef : star c * c = ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ := by
    have hstar : star c = c := by
      rw [hc, star_inv₀]; congr 1; exact Complex.conj_ofReal _
    rw [hstar, hc, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hs]
  rw [becCoherentState, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, hcoef]
  congr 1
  rw [Matrix.mulVec_sum, star_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun M' _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, starRingEnd_apply]
  ring

/-- A **slow `M_max` window** (Tasaki §5.3): an increasing cutoff `M_max(L)` that diverges to
infinity "not too rapidly", staying within the tower range `M_max(L) ≤ C₁ L^{d/2}` for large `L`. -/
def IsSlowBECWindow (d : ℕ) (C₁ : ℝ) (Mmax : ℕ → ℕ) : Prop :=
  Monotone Mmax ∧ Filter.Tendsto Mmax Filter.atTop Filter.atTop ∧
    ∀ᶠ L in Filter.atTop, (Mmax L : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2)

/-- **The BEC coherent-state SSB constants predicate** (Tasaki Theorem 5.3, eqs. (5.3.6)–(5.3.8)).
`IsBECCoherentSSBConstants d μ q₀ C₁ mStar` asserts `√(2 q₀) ≤ mStar` (the `U(1)` bound, eq.
(5.3.6), the `√2` companion of Theorem 4.11's `√3`) and that, for every phase `θ` and every
realizing ground-state family `Φ_L` of the chemical-potential Hamiltonian `Ĥ_μ` (eventual
minimizer/nonzero
with ODLRO `q₀`, whose tower states are nonvanishing throughout the range `|M| ≤ C₁ L^{d/2}`), there
**exists a sufficiently slowly diverging window** `M_max` (`IsSlowBECWindow`) for which the coherent
state `Ξ_θ` exhibits the symmetry-breaking limits — stated in the sound eventual-`ε` form (per
footnote 9, the `lim` is interpreted as genuine eventual convergence along even volumes; the
existential window matches Tasaki's "if `M_max` diverges not too rapidly" and Theorem 4.9's `∃ M`):
* (5.3.7) `⟨Ξ_θ, Ô_L^{(1)} Ξ_θ⟩ / L^d → mStar cos θ` and `⟨Ξ_θ, Ô_L^{(2)} Ξ_θ⟩ / L^d → mStar sin θ`;
* (5.3.8) `⟨Ξ_θ, (Ô_L^{(1)})² Ξ_θ⟩ / (L^d)² → (mStar cos θ)²` and the `(2)` analog
  `→ (mStar sin θ)²`;
* (5.3.6) the complex moments `⟨Ξ_θ, Ô_L^± Ξ_θ⟩ / L^d → mStar e^{±iθ}`. -/
def IsBECCoherentSSBConstants (d : ℕ) (μ q₀ C₁ mStar : ℝ) : Prop :=
  0 < C₁ ∧ 0 ≤ q₀ ∧ 0 < mStar ∧ Real.sqrt (2 * q₀) ≤ mStar ∧
    ∀ (θ : ℝ) (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ),
      (∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
        (xyChemicalPotentialHamiltonianS d L μ).mulVec (Φ L) = E₀ L • Φ L ∧
        (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin 2) → ℂ, Ψ ≠ 0 →
          (xyChemicalPotentialHamiltonianS d L μ).mulVec Ψ = E • Ψ → (E₀ L).re ≤ E.re) ∧
        Φ L ≠ 0 ∧
        (∀ α : Fin 3, α ≠ 2 → q₀ ≤ expectationRatioRe
          ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2) ∧
        (∀ M : ℤ, (M.natAbs : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
          towerState (torusParitySublattice d L) 1 M (Φ L) ≠ 0)) →
      -- there exists a *sufficiently slowly* diverging window for which the SSB limits hold
      ∃ Mmax : ℕ → ℕ, IsSlowBECWindow d C₁ Mmax ∧
      -- (5.3.7): the magnetization-density moments converge to a classical vector of length mStar
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        |expectationRatioRe (staggeredOrderOp1S (torusParitySublattice d L) 1)
            (becCoherentState d L θ (Mmax L) (Φ L)) / (L : ℝ) ^ d - mStar * Real.cos θ| < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        |expectationRatioRe (staggeredOrderOp2S (torusParitySublattice d L) 1)
            (becCoherentState d L θ (Mmax L) (Φ L)) / (L : ℝ) ^ d - mStar * Real.sin θ| < ε) ∧
      -- (5.3.8): the squared moments converge to the squared classical components
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        |expectationRatioRe ((staggeredOrderOp1S (torusParitySublattice d L) 1) ^ 2)
            (becCoherentState d L θ (Mmax L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
          - (mStar * Real.cos θ) ^ 2| < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        |expectationRatioRe ((staggeredOrderOp2S (torusParitySublattice d L) 1) ^ 2)
            (becCoherentState d L θ (Mmax L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
          - (mStar * Real.sin θ) ^ 2| < ε) ∧
      -- (5.3.6): the complex order-operator moments rotate as e^{±iθ}
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        ‖expectationRatioComplex (staggeredRaisingOpS (torusParitySublattice d L) 1)
            (becCoherentState d L θ (Mmax L) (Φ L)) / ((L : ℝ) ^ d : ℂ)
          - (mStar : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        ‖expectationRatioComplex (staggeredLoweringOpS (torusParitySublattice d L) 1)
            (becCoherentState d L θ (Mmax L) (Φ L)) / ((L : ℝ) ^ d : ℂ)
          - (mStar : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)‖ < ε)

/-- **The half-filling BEC coherent-state SSB constants predicate** (Tasaki Theorem 5.3,
eqs. (5.3.5)–(5.3.8), pp. 141–142).  `IsBECCoherentSSBConstantsHalfFilling d q₀ C₁ mStar` is the
`μ = 0` (half-filling) kernel of `IsBECCoherentSSBConstants`: it fixes the chemical potential to
`μ = 0` (so the coherent state is built over the `Ĥ_0 = 2 Ĥ_XY` ground-state tower) and adds, as an
inner premise conjunct, the half-filling sector condition `Ŝ_tot^{(3)} Φ_L = 0` (the same sector
hypothesis as Theorems 5.1/5.2, `tasaki_5_1_xy_odlro_half_filling` and
`IsBECTowerConstantsHalfFilling`).
Under these hypotheses — a realizing family `Φ_L` of nonzero minimal-energy eigenvectors of
`Ĥ_0 = 2 Ĥ_XY` in the `Ŝ_tot^{(3)} = 0` sector exhibiting the two XY-plane ODLRO bounds (`α = 1, 2`)
with parameter `q₀` and nonvanishing tower states throughout `|M| ≤ C₁ L^{d/2}` — there exists a
sufficiently slowly diverging window `M_max` (`IsSlowBECWindow`) for which the coherent state `Ξ_θ`
(`becCoherentState`, eq. (5.3.5)) exhibits the same symmetry-breaking limits as
`IsBECCoherentSSBConstants`, and `√(2 q₀) ≤ mStar` (the `U(1)` `√2` bound, eq. (5.3.6)).

Unlike the general-`μ` `IsBECCoherentSSBConstants` (kept as the faithful documented axiom
`tasaki_5_3_bec_u1_ssb`, whose general-`μ` limits rest on the Koma–Tasaki [21]
reflection-positivity/infrared machinery, intractable at project scale), this half-filling kernel is
the discharge target: at `μ = 0` the reused variational bricks (tower non-vanishing/denominator,
sector orthogonality, the U(1) two-axis base ratio) all require the half-filling
`Ŝ_tot^{(3)} = 0` sector.  A general-`μ` ground state has `Ŝ_tot^{(3)} Φ = s₀ ≠ 0`, so those
bricks no longer close, and this predicate is a genuinely stronger statement (not `α`-equivalent to
`IsBECCoherentSSBConstants`), mirroring the Theorem 5.2 half-filling kernel. -/
def IsBECCoherentSSBConstantsHalfFilling (d : ℕ) (q₀ C₁ mStar : ℝ) : Prop :=
  0 < C₁ ∧ 0 ≤ q₀ ∧ 0 < mStar ∧ Real.sqrt (2 * q₀) ≤ mStar ∧
    ∀ (θ : ℝ) (Φ : (L : ℕ) → (HypercubicTorus d L → Fin 2) → ℂ) (E₀ : ℕ → ℂ),
      (∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
        (xyChemicalPotentialHamiltonianS d L 0).mulVec (Φ L) = E₀ L • Φ L ∧
        (∀ E : ℂ, ∀ Ψ : (HypercubicTorus d L → Fin 2) → ℂ, Ψ ≠ 0 →
          (xyChemicalPotentialHamiltonianS d L 0).mulVec Ψ = E • Ψ → (E₀ L).re ≤ E.re) ∧
        Φ L ≠ 0 ∧
        (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec (Φ L) = 0 ∧
        (∀ α : Fin 3, α ≠ 2 → q₀ ≤ expectationRatioRe
          ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2) ∧
        (∀ M : ℤ, (M.natAbs : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) →
          towerState (torusParitySublattice d L) 1 M (Φ L) ≠ 0)) →
      -- there exists a *sufficiently slowly* diverging window for which the SSB limits hold
      ∃ Mmax : ℕ → ℕ, IsSlowBECWindow d C₁ Mmax ∧
      -- (5.3.7): the magnetization-density moments converge to a classical vector of length mStar
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        |expectationRatioRe (staggeredOrderOp1S (torusParitySublattice d L) 1)
            (becCoherentState d L θ (Mmax L) (Φ L)) / (L : ℝ) ^ d - mStar * Real.cos θ| < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        |expectationRatioRe (staggeredOrderOp2S (torusParitySublattice d L) 1)
            (becCoherentState d L θ (Mmax L) (Φ L)) / (L : ℝ) ^ d - mStar * Real.sin θ| < ε) ∧
      -- (5.3.8): the squared moments converge to the squared classical components
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        |expectationRatioRe ((staggeredOrderOp1S (torusParitySublattice d L) 1) ^ 2)
            (becCoherentState d L θ (Mmax L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
          - (mStar * Real.cos θ) ^ 2| < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        |expectationRatioRe ((staggeredOrderOp2S (torusParitySublattice d L) 1) ^ 2)
            (becCoherentState d L θ (Mmax L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
          - (mStar * Real.sin θ) ^ 2| < ε) ∧
      -- (5.3.6): the complex order-operator moments rotate as e^{±iθ}
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        ‖expectationRatioComplex (staggeredRaisingOpS (torusParitySublattice d L) 1)
            (becCoherentState d L θ (Mmax L) (Φ L)) / ((L : ℝ) ^ d : ℂ)
          - (mStar : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
        ‖expectationRatioComplex (staggeredLoweringOpS (torusParitySublattice d L) 1)
            (becCoherentState d L θ (Mmax L) (Φ L)) / ((L : ℝ) ^ d : ℂ)
          - (mStar : ℂ) * Complex.exp (-(θ : ℂ) * Complex.I)‖ < ε)

/-- **Tasaki Theorem 5.3 (the U(1) symmetry-breaking states of hard-core bosons), AXIOM.**  If the
slow-window cutoff `M_max(L)` diverges to infinity not too rapidly, then the `U(1)` coherent state
`Ξ_θ` (eq. (5.3.5)) fully breaks the phase symmetry: the order-operator density behaves as a
classical planar vector of length `mStar` pointing in the direction `θ`, with vanishing fluctuation
(eqs. (5.3.6)–(5.3.8)), and the order parameter obeys `mStar ≥ √(2 q₀)` (the `U(1)` `√2` bound).

This is the BEC counterpart of the Tanaka full-symmetry-breaking Theorem 4.9; the construction and
constants are bundled into `IsBECCoherentSSBConstants` (`μ` parametrizes the density, as in Theorem
5.2).  Conditional on ODLRO (`q₀ > 0`); the realizing ground-state family supplies the nonvanishing
tower states needed to normalize the `Γ_M`.  Proved in Koma–Tasaki [21]; recorded as a documented
axiom. -/
axiom tasaki_5_3_bec_u1_ssb (d : ℕ) (hd : 2 ≤ d) (μ q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ mStar : ℝ, IsBECCoherentSSBConstants d μ q₀ C₁ mStar

/-! ## Theorem 5.4: symmetry breaking in coupled Bose–Einstein condensates -/

/-- The **coupled (two-species) lattice** `Λ_a ⊔ Λ_b` (Tasaki §5.5): two exact copies of the
hypercubic torus, the site `(x, false)` lying on copy `a` and `(x, true)` on copy `b`.  The combined
hard-core boson Hilbert space is `ManyBodyOpS (CoupledSite d L) 1`; the physical
total-particle-number `2N` sector is the doubled half filling `Ŝ_tot^{(3)} = 0`. -/
abbrev CoupledSite (d L : ℕ) : Type := HypercubicTorus d L × Bool

/-- The **same-species nearest-neighbor coupling** on the coupled lattice: it is the torus
nearest-neighbor coupling between two sites of the *same* species (`a–a` or `b–b`), and `0` across
species.  The XY Hamiltonian built from it is `Ĥ_a + Ĥ_b` (eq. (5.5.2), the two uncoupled
copies). -/
noncomputable def sameSpeciesNNCoupling (d L : ℕ) [NeZero L] (p q : CoupledSite d L) : ℂ :=
  if p.2 = q.2 then torusNNCoupling d L p.1 q.1 else 0

/-- The **tunneling Hamiltonian** `Ĥ_tunnel = −Σ_x (e^{iφ} â_{(x,a)}^† â_{(x,b)} + e^{−iφ} â_{(x,a)}
â_{(x,b)}^†)` (eq. (5.5.3)) that weakly couples the two condensates, in spin form: `â_{(x,a)}^†
â_{(x,b)} ↔ Ŝ_{(x,a)}^+ Ŝ_{(x,b)}^−` (the staggered gauge signs `(−1)^x` cancel at equal `x`). -/
noncomputable def tunnelHamiltonian (d L : ℕ) [NeZero L] (φ : ℝ) :
    ManyBodyOpS (CoupledSite d L) 1 :=
  -∑ x : HypercubicTorus d L,
    (Complex.exp (Complex.I * (φ : ℂ)) •
        (spinSSiteOpPlus (x, false) 1 * spinSSiteOpMinus (x, true) 1) +
      Complex.exp (-(Complex.I * (φ : ℂ))) •
        (spinSSiteOpMinus (x, false) 1 * spinSSiteOpPlus (x, true) 1))

/-- The **total coupled Hamiltonian** `Ĥ_tot^ε = Ĥ_a + Ĥ_b + ε Ĥ_tunnel` (eq. (5.5.1)): the two
uncoupled hard-core boson copies `Ĥ_a + Ĥ_b = 2 (Ĥ_XY,a + Ĥ_XY,b)` (the boson dictionary
`Ĥ = 2 Ĥ_XY`, eq. (5.1.7), consistent with `xyChemicalPotentialHamiltonianS`; via
`sameSpeciesNNCoupling` at
anisotropy `λ = D = 0`) plus the tunneling term of strength `ε ≥ 0`.  The factor `2` keeps `ε` equal
to Tasaki's tunneling strength relative to the boson Hamiltonians. -/
noncomputable def coupledHamiltonian (d L : ℕ) [NeZero L] (φ ε : ℝ) :
    ManyBodyOpS (CoupledSite d L) 1 :=
  (2 : ℂ) • anisotropicHeisenbergS (sameSpeciesNNCoupling d L) 0 0 1 +
    (ε : ℂ) • tunnelHamiltonian d L φ

/-- The **inter-condensate correlation operator** `â_{(x,a)}^† â_{(x,b)}` (the observable of
eqs. (5.5.5)/(5.5.6)), in spin form `Ŝ_{(x,a)}^+ Ŝ_{(x,b)}^−` — it annihilates a particle in
condensate `b` at `x` and creates one in condensate `a` at `x`. -/
noncomputable def coupledCrossCorrelation (d L : ℕ) [NeZero L] (x : HypercubicTorus d L) :
    ManyBodyOpS (CoupledSite d L) 1 :=
  spinSSiteOpPlus (x, false) 1 * spinSSiteOpMinus (x, true) 1

/-- The **conjugate inter-condensate correlation operator** `â_{(x,a)} â_{(x,b)}^†` (the observable
of eq. (5.5.6)), in spin form `Ŝ_{(x,a)}^− Ŝ_{(x,b)}^+` — the adjoint of `coupledCrossCorrelation`,
annihilating a particle in `a` at `x` and creating one in `b` at `x`. -/
noncomputable def coupledCrossCorrelationConj (d L : ℕ) [NeZero L] (x : HypercubicTorus d L) :
    ManyBodyOpS (CoupledSite d L) 1 :=
  spinSSiteOpMinus (x, false) 1 * spinSSiteOpPlus (x, true) 1

/-- **Tasaki Theorem 5.4 (symmetry breaking in coupled Bose–Einstein condensates), AXIOM.**  Two
hard-core boson condensates on copies `Λ_a`, `Λ_b` of the torus are weakly coupled by the tunneling
Hamiltonian (strength `ε`), with the total particle number fixed at `2N` (the doubled half filling
`Ŝ_tot^{(3)} = 0`).  Assuming the single uncoupled system has ODLRO with parameter `q₀ > 0`
(eq. (5.2.5), Theorem 5.1 — supplied as the hypothesis `hODLRO`, which ties `q₀` to the genuine
order parameter of the uncoupled XY ground states), the unique ground state `Φ^ε` develops a
**definite relative `U(1)` phase** between the two condensates: there is an order parameter `m̃`,
with `m̃ ≥ m∗ ≥ √(2 q₀)`, such that for any `x ∈ ℤ^d`
`lim_{ε↓0} lim_{L↑∞} ⟨Φ^ε, â_{(x,a)}^† â_{(x,b)} Φ^ε⟩ / ⟨Φ^ε, Φ^ε⟩ = m̃² e^{−iφ}` (eq. (5.5.5)) and
the conjugate `lim_{ε↓0} lim_{L↑∞} ⟨Φ^ε, â_{(x,a)} â_{(x,b)}^† Φ^ε⟩ / ⟨Φ^ε, Φ^ε⟩ = m̃² e^{+iφ}`
(eq. (5.5.6)).

The two condensates are thus coupled coherently (entangled) with a fixed relative phase `φ`.  The
ground state `Φ^ε` is a *given* family (unique per `(ε, L)` by a Marshall–Lieb–Mattis argument:
eigenvector at the minimal energy, nonzero, in the `2N`-particle sector `Ŝ_tot^{(3)} = 0`).  The
double limit is stated soundly in eventual-`ε'` form (outer `ε↓0`, inner `L↑∞`); `m̃` is existential
with the lower bound `√(2 q₀)`.  Proved in Koma–Tasaki [22]; recorded as a documented axiom.  Unlike
Theorem 5.1, this is a **genuine iterated thermodynamic limit** `lim_{ε↓0} lim_{L↑∞}`: a Tasaki
footnote states that the existence of the limit itself is unproven (open in the source literature),
so it falls under the open-conjecture exclusion of the externally-cited-theorem prove policy, rather
than being a tractable finite-dimensional cite-only case. -/
axiom tasaki_5_4_coupled_bec_ssb (d : ℕ) (hd : 2 ≤ d) (φ q₀ : ℝ) (hq₀ : 0 < q₀)
    (x : Fin d → ℤ)
    -- the single *uncoupled* system has ODLRO with parameter `q₀` (Theorem 5.1, eq. (5.2.5)):
    (hODLRO : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], Even L → L₀ ≤ L →
      ∀ (Ψ : (HypercubicTorus d L → Fin 2) → ℂ) (E : ℂ), Ψ ≠ 0 →
        (xyHamiltonianS d L).mulVec Ψ = E • Ψ →
        (∀ E' : ℂ, ∀ Ξ : (HypercubicTorus d L → Fin 2) → ℂ, Ξ ≠ 0 →
          (xyHamiltonianS d L).mulVec Ξ = E' • Ξ → E.re ≤ E'.re) →
        (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Ψ = 0 →
        ∀ α : Fin 3, α ≠ 2 → q₀ ≤ expectationRatioRe
          ((staggeredOrderOpAxisS α (torusParitySublattice d L) 1) ^ 2) Ψ / ((L : ℝ) ^ d) ^ 2)
    (Φ : ℝ → (L : ℕ) → (CoupledSite d L → Fin 2) → ℂ) (E₀ : ℝ → ℕ → ℂ)
    (hΦ : ∀ ε : ℝ, 0 < ε → ∃ L₁ : ℕ, ∀ (L : ℕ) [NeZero L], L₁ ≤ L → 2 ≤ L → Even L →
      (coupledHamiltonian d L φ ε).mulVec (Φ ε L) = E₀ ε L • Φ ε L ∧
      (∀ E : ℂ, ∀ Ψ : (CoupledSite d L → Fin 2) → ℂ, Ψ ≠ 0 →
        (coupledHamiltonian d L φ ε).mulVec Ψ = E • Ψ → (E₀ ε L).re ≤ E.re) ∧
      Φ ε L ≠ 0 ∧ (totalSpinSOp3 (CoupledSite d L) 1).mulVec (Φ ε L) = 0) :
    ∃ mtilde : ℝ, Real.sqrt (2 * q₀) ≤ mtilde ∧
      ∀ ε' : ℝ, 0 < ε' → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 2 ≤ L → Even L →
          ‖expectationRatioComplex (coupledCrossCorrelation d L (torusEmbed d L x)) (Φ ε L)
            - ((mtilde ^ 2 : ℝ) : ℂ) * Complex.exp (-(Complex.I * (φ : ℂ)))‖ < ε' ∧
          ‖expectationRatioComplex (coupledCrossCorrelationConj d L (torusEmbed d L x)) (Φ ε L)
            - ((mtilde ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * (φ : ℂ))‖ < ε'

end LatticeSystem.Quantum
