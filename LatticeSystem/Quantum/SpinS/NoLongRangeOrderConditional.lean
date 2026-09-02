/-
Conditional absence of long-range order in one dimension, modulo the susceptibility bound
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

Assembling the full Falk–Bruch chain — the `O(L)` oscillator-strength bound, the susceptibility
reduction, and the ground-state eigenvalue bridge — yields the exact `ε`–`δ` statement of Corollary
4.3 *modulo a single asymptotic susceptibility hypothesis*: if the staggered static susceptibility
of every ground state is `o(L³)` (for every target margin `δ > 0` it is eventually `≤ δ·L³`), then
the squared staggered order parameter per site vanishes in the thermodynamic limit,
`lim_{L↑∞} ⟨Φ_GS|(Ô_L/L)²|Φ_GS⟩ = 0`.  This isolates the remaining work for the unconditional
Corollary 4.3 to the sub-cubic susceptibility bound (the `L³`, not `L`, scale is what the Falk–Bruch
chain's `12 N³ L` oscillator-strength factor actually needs).
-/
import LatticeSystem.Quantum.SpinS.StaggeredOrderSusceptibility
import LatticeSystem.Quantum.SpinS.HermitianGroundStateEigenvalue

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- Hermiticity of the zero-field ring Heisenberg Hamiltonian. -/
private theorem ringHeisenberg_isHermitian (L N : ℕ) :
    (heisenbergHamiltonianS (ringCoupling L) N).IsHermitian :=
  heisenbergHamiltonianS_isHermitian_of_real (ringCoupling_self_star L) N

/-- **Conditional Corollary 4.3 (absence of long-range order in one dimension), modulo the
sub-cubic susceptibility bound.**  Suppose the staggered static susceptibility of every normalized
ground state of the zero-field **even** ring is `o(L³)`: for every margin `δ > 0` there is a size
threshold `L₀` beyond which every even `L ≥ max(L₀, 2)` and every
normalized
ground state `Φ` (eigenvalue `hermitianMinEigenvalue`) has a potential `y` for `ÔΦ`
(`(Ĥ − E₀) y = ÔΦ`) with `Re⟨y, ÔΦ⟩ ≤ δ·L³`.  Then the squared staggered order parameter per site
vanishes in the thermodynamic limit: for every `ε > 0` there is `L₀` beyond which every normalized
ground state of an even ring `L ≥ L₀` has `|⟨Φ, Ô² Φ⟩.re / L²| < ε`.  The `Even L` guard is
essential: only bipartite (even) rings carry a balanced staggered sublattice, so `ÔΦ ⊥ Φ` and the
resolvent potential `y` exists; odd rings are non-bipartite and lie outside Tasaki's §4.1
setting. -/
theorem no_long_range_order_1d_of_susceptibility (N : ℕ) (hN : 1 ≤ N)
    (hsusc : ∀ δ : ℝ, 0 < δ → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → 2 ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ, star Φ ⬝ᵥ Φ = 1 →
      (heisenbergHamiltonianS (ringCoupling L) N).mulVec Φ
          = (hermitianMinEigenvalue (ringHeisenberg_isHermitian L N) : ℂ) • Φ →
      ∃ y : (Fin L → Fin (N + 1)) → ℂ,
        (heisenbergHamiltonianS (ringCoupling L) N
            - (hermitianMinEigenvalue (ringHeisenberg_isHermitian L N) : ℂ)
              • (1 : ManyBodyOpS (Fin L) N)).mulVec y
          = (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ
        ∧ (star y ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re
            ≤ δ * (L : ℝ) ^ 3) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → Even L →
      ∀ Φ : (Fin L → Fin (N + 1)) → ℂ, star Φ ⬝ᵥ Φ = 1 →
        (∃ E₀ : ℂ, (staggeredFieldChainHamiltonianS L 0 N).mulVec Φ = E₀ • Φ ∧
          (∀ E : ℂ, ∀ Ψ : (Fin L → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
            (staggeredFieldChainHamiltonianS L 0 N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧
          Φ ≠ 0) →
        |(star Φ ⬝ᵥ ((staggeredOrderOpS (ringStaggeredSublattice L) N *
            staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ)).re / ((L : ℝ) ^ 2)|
          < ε := by
  intro ε hε
  -- `N ≠ 0` as a real number, needed to cancel `N³` against itself below.
  have hNne : (N : ℝ) ≠ 0 := by
    have hN0 : N ≠ 0 := by omega
    exact_mod_cast hN0
  -- the margin that recovers a *strict* `<` at the end: `δ := ε²/(24·N³)`.
  have hδpos : 0 < ε ^ 2 / (24 * (N : ℝ) ^ 3) := by positivity
  obtain ⟨L₀, hL₀⟩ := hsusc (ε ^ 2 / (24 * (N : ℝ) ^ 3)) hδpos
  refine ⟨max L₀ 2, fun L hL hLeven Φ hΦnorm hgs => ?_⟩
  have hLL₀ : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : 2 ≤ L := le_trans (le_max_right _ _) hL
  haveI : NeZero L := ⟨by omega⟩
  -- zero-field Hamiltonian = the ring Heisenberg Hamiltonian
  have hzero : staggeredFieldChainHamiltonianS L 0 N
      = heisenbergHamiltonianS (ringCoupling L) N := by
    simp [staggeredFieldChainHamiltonianS]
  obtain ⟨E₀, heig, hmin, _⟩ := hgs
  rw [hzero] at heig hmin
  -- ground-state eigenvalue bridge
  have hHeig := groundState_mulVec_eq_hermitianMinEigenvalue (ringHeisenberg_isHermitian L N)
    hΦnorm heig hmin
  -- sub-cubic susceptibility potential at margin `δ = ε²/(24 N³)`
  obtain ⟨y, hy, hχ⟩ := hL₀ L hLL₀ hL2 hLeven Φ hΦnorm hHeig
  -- Falk–Bruch + oscillator: `2 (⟨Ô²⟩.re)² ≤ 12 N³ L · χ`
  have hpr68 := staggeredOrder_sq_le_susceptibility L N hL2 hN hΦnorm hHeig hy
  set s := (star Φ ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N
      * staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re with hs
  set χ := (star y ⬝ᵥ (staggeredOrderOpS (ringStaggeredSublattice L) N).mulVec Φ).re with hχdef
  -- `s ≥ 0` (= ‖ÔΦ‖²)
  have hs_nonneg : 0 ≤ s := by
    rw [hs, hermitian_dotProduct_shift (staggeredOrderOpS_isHermitian _ N) Φ]
    exact (Complex.le_def.mp (dotProduct_star_self_nonneg _)).1
  have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  -- `12 N³ L · χ ≤ 12 N³ L · (δ · L³) = (ε²/2) · L⁴`, cancelling the `N³` factors.
  have hδL3 : 12 * (N : ℝ) ^ 3 * (L : ℝ) * χ
      ≤ 12 * (N : ℝ) ^ 3 * (L : ℝ) * ((ε ^ 2 / (24 * (N : ℝ) ^ 3)) * (L : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hχ (by positivity)
  have hcollapse : 12 * (N : ℝ) ^ 3 * (L : ℝ) * ((ε ^ 2 / (24 * (N : ℝ) ^ 3)) * (L : ℝ) ^ 3)
      = (ε ^ 2 / 2) * (L : ℝ) ^ 4 := by
    field_simp
    ring
  -- `s² ≤ (ε²/4) · L⁴`
  have hsq : s ^ 2 ≤ (ε ^ 2 / 4) * (L : ℝ) ^ 4 := by linarith [hpr68, hδL3, hcollapse]
  -- `(ε²/4)·L⁴ < ε²·L⁴ = (ε·L²)²`, so the bound is strict.
  have hL4pos : (0 : ℝ) < (L : ℝ) ^ 4 := by positivity
  have hεsqpos : (0 : ℝ) < ε ^ 2 := by positivity
  have hexpand : (ε * (L : ℝ) ^ 2) ^ 2 = ε ^ 2 * (L : ℝ) ^ 4 := by ring
  have hstep : (ε ^ 2 / 4) * (L : ℝ) ^ 4 < (ε * (L : ℝ) ^ 2) ^ 2 := by
    rw [hexpand]; nlinarith [hεsqpos, hL4pos]
  have hub : s ^ 2 < (ε * (L : ℝ) ^ 2) ^ 2 := lt_of_le_of_lt hsq hstep
  have hεpos : 0 < ε * (L : ℝ) ^ 2 := by positivity
  -- conclude `|s / L²| < ε`
  rw [abs_of_nonneg (div_nonneg hs_nonneg (by positivity)), div_lt_iff₀ (by positivity)]
  nlinarith [hub, hs_nonneg, hεpos]

end LatticeSystem.Quantum
